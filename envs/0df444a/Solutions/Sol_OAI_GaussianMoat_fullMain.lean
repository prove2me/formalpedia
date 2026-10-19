-- Prove2me | solution 1 for OAI.GaussianMoat.fullMain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T16:03:45.965926+00:00
-- url     : https://prove2.me/submissions/b6d40c91-8bcb-424b-8b9d-be6fc578c054

import Mathlib
import Definitions.Def_GaussianMoat

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
alias Finset.prod_le_prod₀ := Finset.prod_le_prod
end OAICompat434

universe uIota uAlpha uBeta uGamma uOmega uDelta uEpsilon uZeta uKappa uXi uCapitalKappa uGroup uCapitalGamma uGroupPrime uOutput uAlphaPrime uBetaPrime uGammaPrime uCapitalGammaPrime

section
section
namespace OAI

namespace GaussianMoat

end GaussianMoat

end OAI
end
end

section
section
namespace OAI

namespace GaussianMoat

def determinant (z w : GaussianInt) : ℤ := z.re * w.im - z.im * w.re

theorem determinant_mul_left (a z w : GaussianInt) :
    determinant (a * z) (a * w) = a.norm * determinant z w := by
  simp only [determinant, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.norm]
  ring

theorem norm_dvd_determinant {a z w : GaussianInt} (hz : a ∣ z) (hw : a ∣ w) :
    a.norm ∣ determinant z w := by
  obtain ⟨u, rfl⟩ := hz
  obtain ⟨v, rfl⟩ := hw
  rw [determinant_mul_left]
  exact dvd_mul_right _ _

theorem determinant_eq_zero_of_common_factor {a z w : GaussianInt}
    (hz : a ∣ z) (hw : a ∣ w) (hsmall : |determinant z w| < a.norm) :
    determinant z w = 0 := by
  by_contra hne
  have hpos : 0 < |determinant z w| := abs_pos.mpr hne
  have hdiv : a.norm ∣ |determinant z w| := (dvd_abs _ _).mpr (norm_dvd_determinant hz hw)
  have hle := Int.le_of_dvd hpos hdiv
  omega

structure SplitSieve where
  primes : Finset ℕ
  factor : ℕ → GaussianInt
  prime_mem : ∀ p ∈ primes, Nat.Prime p
  mod_four : ∀ p ∈ primes, p % 4 = 1
  factor_irreducible : ∀ p ∈ primes, Irreducible (factor p)
  factor_norm : ∀ p ∈ primes, (factor p).norm = (p : ℤ)

def SplitSieve.avoiding (s : SplitSieve) : Set GaussianInt :=
  {z | ∀ p ∈ s.primes, ¬s.factor p ∣ z ∧ ¬star (s.factor p) ∣ z}

def FiniteSieveEndpoint : Prop :=
  ∀ D : ℝ, 1 ≤ D → ∃ s : SplitSieve,
    ∀ z : ℕ → GaussianInt, (∀ t, z t ∈ s.avoiding) → Function.Injective z →
      (∀ t, dist (z (t + 1) : ℂ) (z t : ℂ) ≤ D) → False

theorem finite_box (N : ℤ) :
    {z : GaussianInt | |z.re| ≤ N ∧ |z.im| ≤ N}.Finite := by
  have hinj : Function.Injective (fun z : GaussianInt => (z.re, z.im)) := by
    intro z w h
    exact Zsqrtd.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hf := (Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N)
  apply (hf.preimage hinj.injOn).subset
  intro z hz
  exact ⟨abs_le.mp hz.1, abs_le.mp hz.2⟩

theorem finite_norm_le (N : ℤ) : {z : GaussianInt | z.norm ≤ N}.Finite := by
  apply (finite_box (|N| + 1)).subset
  intro z hz
  have heq : z.norm = z.re ^ 2 + z.im ^ 2 := by
    simp only [Zsqrtd.norm]
    ring
  have hn : N ≤ |N| := le_abs_self N
  have hn0 : 0 ≤ |N| := abs_nonneg N
  have hx : z.re ^ 2 ≤ (|N| + 1)^2 := by
    change z.norm ≤ N at hz
    linarith [sq_nonneg z.im, sq_nonneg (|N| : ℤ)]
  have hy : z.im ^ 2 ≤ (|N| + 1)^2 := by
    change z.norm ≤ N at hz
    linarith [sq_nonneg z.re, sq_nonneg (|N| : ℤ)]
  exact ⟨abs_le_of_sq_le_sq hx (by omega), abs_le_of_sq_le_sq hy (by omega)⟩

theorem finite_irreducibles_divisible (a : GaussianInt) (ha : Irreducible a) :
    {z : GaussianInt | Irreducible z ∧ a ∣ z}.Finite := by
  apply (finite_norm_le a.norm).subset
  intro z hz
  exact (Zsqrtd.norm_eq_of_associated (by decide) (ha.associated_of_dvd hz.1 hz.2)).ge

def SplitSieve.exceptions (s : SplitSieve) : Set GaussianInt :=
  {z | Irreducible z ∧ z ∉ s.avoiding}

theorem SplitSieve.exceptions_finite (s : SplitSieve) : s.exceptions.Finite := by
  have hfactor (p : ℕ) (hp : p ∈ s.primes) :
      {z : GaussianInt | Irreducible z ∧
        (s.factor p ∣ z ∨ star (s.factor p) ∣ z)}.Finite := by
    have hstar : Irreducible (star (s.factor p)) :=
      (MulEquiv.irreducible_iff (starRingAut : RingAut GaussianInt)).mpr
        (s.factor_irreducible p hp)
    simpa only [← Set.ofPred_or, and_or_left] using
      (finite_irreducibles_divisible (s.factor p) (s.factor_irreducible p hp)).union
        (finite_irreducibles_divisible (star (s.factor p)) hstar)
  apply ((s.primes.finite_toSet).biUnion hfactor).subset
  intro z hz
  obtain ⟨hzprime, hzavoid⟩ := hz
  simp only [SplitSieve.avoiding, Set.mem_ofPred_eq, not_forall, not_and, not_not] at hzavoid
  obtain ⟨p, hp, hdiv⟩ := hzavoid
  exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, ⟨hzprime, by tauto⟩⟩⟩

theorem SplitSieve.eventually_avoiding (s : SplitSieve) (z : ℕ → GaussianInt)
    (hz : ∀ t, Irreducible (z t)) (hinj : Function.Injective z) :
    ∃ N : ℕ, ∀ t, N ≤ t → z t ∈ s.avoiding := by
  have hf : (z ⁻¹' s.exceptions).Finite := s.exceptions_finite.preimage hinj.injOn
  obtain ⟨N, hN⟩ := hf.exists_le
  refine ⟨N + 1, ?_⟩
  intro t ht
  by_contra h
  have ht' : t ∈ z ⁻¹' s.exceptions := ⟨hz t, h⟩
  have := hN t ht'
  omega

theorem main_of_finiteSieve (hsieve : FiniteSieveEndpoint) : MainEndpoint := by
  intro D z hz hinj hstep
  obtain ⟨s, hs⟩ := hsieve (max D 1) (le_max_right _ _)
  obtain ⟨N, hN⟩ := s.eventually_avoiding z hz hinj
  apply hs (fun t => z (N + t))
  · intro t
    exact hN _ (Nat.le_add_right _ _)
  · exact hinj.comp (fun _ _ h => Nat.add_left_cancel h)
  · intro t
    have hh : dist (z (N + (t + 1)) : ℂ) (z (N + t) : ℂ) ≤ D := by
      simpa only [Nat.add_assoc] using hstep (N + t)
    exact hh.trans (le_max_left _ _)

theorem norm_square_complex (z : GaussianInt) : (z.norm : ℝ) = ‖(z : ℂ)‖ ^ 2 := by
  rw [GaussianInt.intCast_real_norm, Complex.normSq_eq_norm_sq]

theorem finite_dist_le (c : GaussianInt) (D : ℝ) :
    {z : GaussianInt | dist (z : ℂ) (c : ℂ) ≤ D}.Finite := by
  let N : ℤ := ⌈D + ‖(c : ℂ)‖⌉
  apply (finite_box N).subset
  intro z hz
  change dist (z : ℂ) (c : ℂ) ≤ D at hz
  have htri : ‖(z : ℂ)‖ ≤ dist (z : ℂ) (c : ℂ) + ‖(c : ℂ)‖ := by
    simpa only [sub_add_cancel, ← dist_eq_norm] using
      norm_add_le ((z : ℂ) - (c : ℂ)) (c : ℂ)
  have hnorm : ‖(z : ℂ)‖ ≤ (N : ℝ) := by
    calc
      ‖(z : ℂ)‖ ≤ dist (z : ℂ) (c : ℂ) + ‖(c : ℂ)‖ := htri
      _ ≤ D + ‖(c : ℂ)‖ := add_le_add_left hz _
      _ ≤ (N : ℝ) := Int.le_ceil _
  constructor
  · have h := (Complex.abs_re_le_norm (z : ℂ)).trans hnorm
    rw [← GaussianInt.intCast_re, ← Int.cast_abs] at h
    exact Int.cast_le.mp h
  · have h := (Complex.abs_im_le_norm (z : ℂ)).trans hnorm
    rw [← GaussianInt.intCast_im, ← Int.cast_abs] at h
    exact Int.cast_le.mp h

theorem norm_le_of_dvd {a z : GaussianInt} (hz : z ≠ 0) (h : a ∣ z) :
    a.norm ≤ z.norm := by
  obtain ⟨w, rfl⟩ := h
  have hw : w ≠ 0 := by
    intro h
    apply hz
    rw [h, mul_zero]
  have hpos : 0 < w.norm := GaussianInt.norm_pos.mpr hw
  rw [Zsqrtd.norm_mul]
  nlinarith [GaussianInt.norm_nonneg a]

theorem not_dvd_sub_of_dist_sq_lt {a z w : GaussianInt} (hzw : z ≠ w)
    (hshort : dist (z : ℂ) (w : ℂ) ^ 2 < (a.norm : ℝ)) : ¬a ∣ z - w := by
  intro hdiv
  have hnorm := norm_le_of_dvd (sub_ne_zero.mpr hzw) hdiv
  have hreal : (a.norm : ℝ) ≤ ((z - w).norm : ℝ) := by exact_mod_cast hnorm
  rw [norm_square_complex (z - w), GaussianInt.toComplex_sub, ← dist_eq_norm] at hreal
  exact (not_lt_of_ge hreal) hshort

noncomputable def latticeGraph (A : Set GaussianInt) (D : ℝ) : SimpleGraph GaussianInt where
  Adj z w := z ≠ w ∧ z ∈ A ∧ w ∈ A ∧ dist (z : ℂ) (w : ℂ) ≤ D
  symm := by
    constructor
    intro z w h
    exact ⟨h.1.symm, h.2.2.1, h.2.1, by simpa only [dist_comm] using h.2.2.2⟩
  loopless := by
    constructor
    intro z h
    exact h.1 rfl

theorem lattice_walk_mem {A : Set GaussianInt} {D : ℝ} {z w : GaussianInt}
    (p : (latticeGraph A D).Walk z w) (hz : z ∈ A) (i : ℕ) : p.getVert i ∈ A := by
  induction p generalizing i with
  | nil => simpa using hz
  | @cons u v w huv p ih =>
    cases i with
    | zero => simpa using hz
    | succ i => exact ih huv.2.2.1 i

theorem lattice_walk_dist {A : Set GaussianInt} {D : ℝ} {z w : GaussianInt}
    (p : (latticeGraph A D).Walk z w) :
    dist (z : ℂ) (w : ℂ) ≤ (p.length : ℝ) * max D 0 := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    calc
      dist (u : ℂ) (w : ℂ) ≤ dist (u : ℂ) (v : ℂ) + dist (v : ℂ) (w : ℂ) :=
        dist_triangle _ _ _
      _ ≤ D + (p.length : ℝ) * max D 0 := add_le_add huv.2.2.2 ih
      _ ≤ ((p.cons huv).length : ℝ) * max D 0 := by
        simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
        linarith [le_max_left D 0]

@[ext]
structure LatticePrefix (A : Set GaussianInt) (D : ℝ) (root : GaussianInt) (n : ℕ) where
  point : Fin (n + 1) → GaussianInt
  mem : ∀ i, point i ∈ A
  start : point 0 = root
  injective : Function.Injective point
  step : ∀ i j, j.val = i.val + 1 → dist (point j : ℂ) (point i : ℂ) ≤ D

theorem LatticePrefix.dist_le {A : Set GaussianInt} {D : ℝ} {root : GaussianInt}
    {n : ℕ} (p : LatticePrefix A D root n) (i : Fin (n + 1)) :
    dist (p.point i : ℂ) (root : ℂ) ≤ (i.val : ℝ) * max D 0 := by
  induction i using Fin.induction with
  | zero => simp [p.start]
  | succ i ih =>
    calc
      dist (p.point i.succ : ℂ) (root : ℂ) ≤
          dist (p.point i.succ : ℂ) (p.point i.castSucc : ℂ) +
            dist (p.point i.castSucc : ℂ) (root : ℂ) := dist_triangle _ _ _
      _ ≤ D + (i.val : ℝ) * max D 0 := add_le_add (p.step _ _ rfl) ih
      _ ≤ (i.succ.val : ℝ) * max D 0 := by
        simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
        linarith [le_max_left D 0]

instance LatticePrefix.finite (A : Set GaussianInt) (D : ℝ) (root : GaussianInt) (n : ℕ) :
    Finite (LatticePrefix A D root n) := by
  let S : Set (Fin (n + 1) → GaussianInt) :=
    {f | ∀ i, dist (f i : ℂ) (root : ℂ) ≤ (n : ℝ) * max D 0}
  have hS : S.Finite := Set.Finite.pi' (fun _ => finite_dist_le root ((n : ℝ) * max D 0))
  let := hS.to_subtype
  let f : LatticePrefix A D root n → S := fun p => ⟨p.point, fun i =>
    (p.dist_le i).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.le_of_lt_succ i.isLt) (le_max_right D 0))⟩
  exact Finite.of_injective f (fun p q h => LatticePrefix.ext (congrArg Subtype.val h))

def LatticePrefix.restrict {A : Set GaussianInt} {D : ℝ} {root : GaussianInt}
    {n m : ℕ} (h : n ≤ m) (p : LatticePrefix A D root m) : LatticePrefix A D root n where
  point i := p.point (Fin.castLE (by omega) i)
  mem i := p.mem _
  start := by simpa using p.start
  injective := p.injective.comp (Fin.castLE_injective (by omega))
  step i j hij := p.step _ _ hij

theorem infinite_component_has_walk {A : Set GaussianInt} {D : ℝ} {root : GaussianInt}
    (hroot : root ∈ A) (hinfinite : {w | (latticeGraph A D).Reachable root w}.Infinite) :
    ∃ z : ℕ → GaussianInt, (∀ n, z n ∈ A) ∧ Function.Injective z ∧
      ∀ n, dist (z (n + 1) : ℂ) (z n : ℂ) ≤ D := by
  classical
  have hne (n : ℕ) : Nonempty (LatticePrefix A D root n) := by
    have hnot : ¬ {w | (latticeGraph A D).Reachable root w} ⊆
        {w | dist (w : ℂ) (root : ℂ) ≤ (n : ℝ) * max D 0} := by
      intro h
      exact hinfinite ((finite_dist_le root ((n : ℝ) * max D 0)).subset h)
    obtain ⟨w, hw, hfar⟩ := Set.not_subset.mp hnot
    apply hw.elim_path
    intro path
    let p := path.val
    have hn : n ≤ p.length := by
      by_contra hn
      have hlen : (p.length : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : p.length ≤ n)
      have hdist := (lattice_walk_dist p).trans
        (mul_le_mul_of_nonneg_right hlen (le_max_right D 0))
      apply hfar
      change dist (w : ℂ) (root : ℂ) ≤ (n : ℝ) * max D 0
      simpa only [dist_comm] using hdist
    exact ⟨{
      point := fun i => p.getVert i.val
      mem := fun i => lattice_walk_mem p hroot _
      start := p.getVert_zero
      injective := fun i j h => Fin.ext (path.isPath.getVert_injOn
        (show i.val ≤ p.length from (Nat.le_of_lt_succ i.isLt).trans hn)
        (show j.val ≤ p.length from (Nat.le_of_lt_succ j.isLt).trans hn) h)
      step := fun i j h => by
        have hadj := p.adj_getVert_succ (i := i.val) (by omega)
        simpa only [h, dist_comm] using hadj.2.2.2
    }⟩
  let (n : ℕ) : Nonempty (LatticePrefix A D root n) := hne n
  obtain ⟨p, hp⟩ := exists_seq_forall_proj_of_forall_finite
    (α := fun n => LatticePrefix A D root n)
    (fun h => LatticePrefix.restrict h)
    (by intro n a; apply LatticePrefix.ext; funext i; rfl)
    (by intro i j k hij hjk a; apply LatticePrefix.ext; funext l; rfl)
    (fun _ _ => Set.toFinite _)
  let z : ℕ → GaussianInt := fun n => (p n).point (Fin.last n)
  have hagree (n k : ℕ) (hnk : n ≤ k) :
      (p k).point ⟨n, by omega⟩ = z n := by
    simpa only [LatticePrefix.restrict, z, Fin.last, Fin.castLE] using
      congrArg (fun a : LatticePrefix A D root n => a.point (Fin.last n)) (hp hnk)
  refine ⟨z, fun n => (p n).mem _, ?_, ?_⟩
  · intro n m heq
    have h := (hagree n (max n m) (le_max_left _ _)).trans
      (heq.trans (hagree m (max n m) (le_max_right _ _)).symm)
    exact congrArg Fin.val ((p (max n m)).injective h)
  · intro n
    have h := (p (n + 1)).step ⟨n, by omega⟩ (Fin.last (n + 1)) rfl
    simpa only [hagree n (n + 1) (by omega)] using h

theorem lattice_component_finite {A : Set GaussianInt} {D : ℝ}
    (hno : ∀ z : ℕ → GaussianInt, (∀ n, z n ∈ A) → Function.Injective z →
      (∀ n, dist (z (n + 1) : ℂ) (z n : ℂ) ≤ D) → False)
    {root : GaussianInt} (hroot : root ∈ A) :
    {w | (latticeGraph A D).Reachable root w}.Finite := by
  by_contra h
  obtain ⟨z, hz, hinj, hstep⟩ := infinite_component_has_walk hroot h
  exact hno z hz hinj hstep

def latticeTranslation {A : Set GaussianInt} {D : ℝ} (v : GaussianInt)
    (hv : ∀ z ∈ A, z + v ∈ A) :
    latticeGraph A D →g latticeGraph A D where
  toFun z := z + v
  map_rel' := by
    intro z w h
    refine ⟨fun he => h.1 (add_right_cancel he), hv z h.2.1, hv w h.2.2.1, ?_⟩
    simpa only [map_add, dist_add_right] using h.2.2.2

theorem eq_of_finite_component_period {A : Set GaussianInt} {D : ℝ}
    {root x y v : GaussianInt}
    (hfinite : {w | (latticeGraph A D).Reachable root w}.Finite)
    (hx : (latticeGraph A D).Reachable root x)
    (hy : (latticeGraph A D).Reachable root y)
    (hv : ∀ z ∈ A, z + v ∈ A) (hxy : y = x + v) : x = y := by
  classical
  by_contra hne
  have hv0 : v ≠ 0 := by intro h; apply hne; simpa [h] using hxy.symm
  have hreach : (latticeGraph A D).Reachable x (x + v) := by
    rw [← hxy]
    exact hx.symm.trans hy
  have hall (n : ℕ) : (latticeGraph A D).Reachable x (x + n • v) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have ht := ih.map (latticeTranslation v hv)
      have hh := hreach.trans ht
      change (latticeGraph A D).Reachable x ((x + n • v) + v) at hh
      simpa only [succ_nsmul, add_assoc] using hh
  have hinj : Function.Injective (fun n : ℕ => x + n • v) := by
    intro n m h
    have hh := add_left_cancel h
    simp only [nsmul_eq_mul] at hh
    exact Nat.cast_injective (mul_right_cancel₀ hv0 hh)
  apply (Set.infinite_range_of_injective hinj)
  exact hfinite.subset (by rintro _ ⟨n, rfl⟩; exact hx.trans (hall n))

def SplitSieve.period (s : SplitSieve) : ℕ := ∏ p ∈ s.primes, p

theorem SplitSieve.period_pos (s : SplitSieve) : 0 < s.period := by
  exact Finset.prod_pos (fun p hp => (s.prime_mem p hp).pos)

theorem SplitSieve.factor_dvd_period (s : SplitSieve) {p : ℕ} (hp : p ∈ s.primes) :
    s.factor p ∣ (s.period : GaussianInt) ∧ star (s.factor p) ∣ (s.period : GaussianInt) := by
  have hn : (p : GaussianInt) = s.factor p * star (s.factor p) := by
    rw [← Zsqrtd.norm_eq_mul_conj, s.factor_norm p hp]
    simp
  have hd : (p : GaussianInt) ∣ (s.period : GaussianInt) := by
    have hh : p ∣ s.period := Finset.dvd_prod_of_mem (fun p : ℕ => p) hp
    exact map_dvd (Nat.castRingHom GaussianInt) hh
  constructor
  · apply dvd_trans _ hd
    rw [hn]
    exact dvd_mul_right _ _
  · apply dvd_trans _ hd
    rw [hn]
    exact dvd_mul_left _ _

theorem SplitSieve.periodic (s : SplitSieve) (z v : GaussianInt) (hz : z ∈ s.avoiding) :
    z + (s.period : GaussianInt) * v ∈ s.avoiding := by
  intro p hp
  have hd := s.factor_dvd_period hp
  constructor
  · intro h
    apply (hz p hp).1
    have hh := dvd_sub h (dvd_mul_of_dvd_left hd.1 v)
    simpa only [add_sub_cancel_right] using hh
  · intro h
    apply (hz p hp).2
    have hh := dvd_sub h (dvd_mul_of_dvd_left hd.2 v)
    simpa only [add_sub_cancel_right] using hh

def residue (Q : ℕ) (z : GaussianInt) : ZMod Q × ZMod Q := (z.re, z.im)

theorem eq_add_period_of_residue_eq {Q : ℕ} {x y : GaussianInt}
    (h : residue Q x = residue Q y) :
    ∃ v : GaussianInt, y = x + (Q : GaussianInt) * v := by
  have hx := (ZMod.intCast_eq_intCast_iff_dvd_sub x.re y.re Q).mp (congrArg Prod.fst h)
  have hy := (ZMod.intCast_eq_intCast_iff_dvd_sub x.im y.im Q).mp (congrArg Prod.snd h)
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨⟨a, b⟩, ?_⟩
  ext <;> simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_mul, Zsqrtd.im_mul,
    Zsqrtd.re_natCast, Zsqrtd.im_natCast, zero_mul, mul_zero, add_zero] <;> omega

theorem periodic_component_bound {A : Set GaussianInt} {D : ℝ} {Q : ℕ} (hQ : Q ≠ 0)
    (hperiod : ∀ z ∈ A, ∀ v : GaussianInt, z + (Q : GaussianInt) * v ∈ A)
    {root : GaussianInt}
    (hfinite : {w | (latticeGraph A D).Reachable root w}.Finite) :
    {w | (latticeGraph A D).Reachable root w}.ncard ≤ Q ^ 2 := by
  classical
  let : NeZero Q := ⟨hQ⟩
  let C := {w | (latticeGraph A D).Reachable root w}
  have hinj : Set.InjOn (residue Q) C := by
    intro x hx y hy heq
    obtain ⟨v, hv⟩ := eq_add_period_of_residue_eq heq
    exact eq_of_finite_component_period hfinite hx hy
      (fun z hz => hperiod z hz v) hv
  have hcard := Set.ncard_le_card ((residue Q) '' C)
  rw [Set.InjOn.ncard_image hinj, Nat.card_prod, Nat.card_zmod, pow_two] at *
  exact hcard

def SplitSieve.boundary (s : SplitSieve) (D : ℝ) : Set GaussianInt :=
  {z | z ∈ s.avoiding ∧ ∃ e ∈ s.exceptions, dist (z : ℂ) (e : ℂ) ≤ D}

theorem SplitSieve.boundary_finite (s : SplitSieve) (D : ℝ) : (s.boundary D).Finite := by
  apply (s.exceptions_finite.biUnion (fun e _ => finite_dist_le e D)).subset
  rintro z ⟨_, e, he, hd⟩
  exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨he, hd⟩⟩

def SplitSieve.restored (s : SplitSieve) (D : ℝ) : Set GaussianInt :=
  s.exceptions ∪ ⋃ v ∈ s.boundary D, {w | (latticeGraph s.avoiding D).Reachable v w}

theorem SplitSieve.restored_finite (s : SplitSieve) (D : ℝ)
    (hf : ∀ r ∈ s.avoiding, {w | (latticeGraph s.avoiding D).Reachable r w}.Finite) :
    (s.restored D).Finite := by
  exact s.exceptions_finite.union ((s.boundary_finite D).biUnion (fun _ hv => hf _ hv.1))

theorem lattice_reachable_mem {A : Set GaussianInt} {D : ℝ} {r w : GaussianInt}
    (hr : r ∈ A) (h : (latticeGraph A D).Reachable r w) : w ∈ A := by
  apply h.elim
  intro p
  simpa only [p.getVert_length] using lattice_walk_mem p hr p.length

theorem SplitSieve.restored_closed (s : SplitSieve) (D : ℝ)
    {p q : PrimeVertex} (hp : p.val ∈ s.restored D) (hadj : (primeGraph D).Adj p q) :
    q.val ∈ s.restored D := by
  classical
  by_cases hqa : q.val ∈ s.avoiding
  · rcases hp with hpe | hp
    · exact Or.inr (Set.mem_iUnion.mpr ⟨q.val, Set.mem_iUnion.mpr
        ⟨⟨hqa, p.val, hpe, by simpa only [dist_comm] using hadj.2⟩,
          SimpleGraph.Reachable.refl _⟩⟩)
    · obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hp
      obtain ⟨hvb, hvp⟩ := Set.mem_iUnion.mp hv
      have hpa := lattice_reachable_mem hvb.1 hvp
      have hed : (latticeGraph s.avoiding D).Adj p.val q.val :=
        ⟨fun h => hadj.1 (Subtype.ext h), hpa, hqa, hadj.2⟩
      exact Or.inr (Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hvb,
        hvp.trans hed.reachable⟩⟩)
  · exact Or.inl ⟨q.property, hqa⟩

theorem prime_reachable_mem {D : ℝ} {T : Set GaussianInt}
    (hclosed : ∀ p q : PrimeVertex, p.val ∈ T → (primeGraph D).Adj p q → q.val ∈ T)
    {p q : PrimeVertex} (hp : p.val ∈ T) (h : (primeGraph D).Reachable p q) : q.val ∈ T := by
  apply h.elim
  intro w
  clear h
  induction w with
  | nil => exact hp
  | @cons a b c hab w ih => exact ih (hclosed a b hp hab)

theorem lattice_component_eq_singleton {A : Set GaussianInt} {D : ℝ} {r : GaussianInt}
    (hr : r ∉ A) : {w | (latticeGraph A D).Reachable r w} = {r} := by
  ext w
  constructor
  · intro h
    apply h.elim
    intro p
    cases p with
    | nil => rfl
    | cons hed p => exact (hr hed.2.1).elim
  · intro h
    rw [Set.mem_singleton_iff] at h
    subst w
    exact SimpleGraph.Reachable.refl _

theorem SplitSieve.component_subset (s : SplitSieve) (D : ℝ) (p : PrimeVertex) :
    Subtype.val '' component D p ⊆
      {w | (latticeGraph s.avoiding D).Reachable p.val w} ∪ s.restored D := by
  rintro _ ⟨q, hq, rfl⟩
  apply prime_reachable_mem (T :=
    {w | (latticeGraph s.avoiding D).Reachable p.val w} ∪ s.restored D) _
    (Or.inl (SimpleGraph.Reachable.refl _)) hq
  intro a b ha hab
  rcases ha with ha | ha
  · by_cases hpa : p.val ∈ s.avoiding
    · by_cases hba : b.val ∈ s.avoiding
      · exact Or.inl (ha.trans (show (latticeGraph s.avoiding D).Adj a.val b.val from
          ⟨fun hh => hab.1 (Subtype.ext hh), lattice_reachable_mem hpa ha, hba, hab.2⟩).reachable)
      · exact Or.inr (Or.inl ⟨b.property, hba⟩)
    · have hap : a.val = p.val := by
        have hh : a.val ∈ {w | (latticeGraph s.avoiding D).Reachable p.val w} := ha
        rw [lattice_component_eq_singleton hpa] at hh
        exact hh
      exact Or.inr (s.restored_closed D (Or.inl (by simpa only [hap] using
        (show p.val ∈ s.exceptions from ⟨p.property, hpa⟩))) hab)
  · exact Or.inr (s.restored_closed D ha hab)

theorem prime_components_of_finiteSieve (hsieve : FiniteSieveEndpoint) (D : ℝ) :
    ∃ B : ℕ, ∀ p : PrimeVertex, (component D p).Finite ∧ (component D p).ncard ≤ B := by
  classical
  obtain ⟨s, hs⟩ := hsieve (max D 1) (le_max_right _ _)
  have hno : ∀ z : ℕ → GaussianInt, (∀ n, z n ∈ s.avoiding) → Function.Injective z →
      (∀ n, dist (z (n + 1) : ℂ) (z n : ℂ) ≤ D) → False := by
    intro z hz hinj hstep
    exact hs z hz hinj (fun n => (hstep n).trans (le_max_left _ _))
  have hf (r : GaussianInt) : {w | (latticeGraph s.avoiding D).Reachable r w}.Finite := by
    by_cases hr : r ∈ s.avoiding
    · exact lattice_component_finite hno hr
    · rw [lattice_component_eq_singleton hr]
      exact Set.finite_singleton _
  have hK := s.restored_finite D (fun r _ => hf r)
  refine ⟨s.period ^ 2 + (s.restored D).ncard, fun p => ?_⟩
  let C := {w | (latticeGraph s.avoiding D).Reachable p.val w}
  have hC : C.ncard ≤ s.period ^ 2 := periodic_component_bound
    (Nat.ne_of_gt s.period_pos) (fun z hz v => s.periodic z v hz) (hf p.val)
  have hsubset := s.component_subset D p
  have hfinimage := ((hf p.val).union hK).subset hsubset
  have hfin : (component D p).Finite := by
    apply (hfinimage.preimage Subtype.val_injective.injOn).subset
    intro q hq
    exact ⟨q, hq, rfl⟩
  refine ⟨hfin, ?_⟩
  have hle := (Set.ncard_le_ncard hsubset ((hf p.val).union hK)).trans
    (Set.ncard_union_le C (s.restored D))
  rw [Set.InjOn.ncard_image Subtype.val_injective.injOn] at hle
  exact hle.trans (Nat.add_le_add_right hC _)

theorem finite_prime_walk_bound {D : ℝ} {B : ℕ}
    (hB : ∀ p : PrimeVertex, (component D p).Finite ∧ (component D p).ncard ≤ B)
    (n : ℕ) (z : Fin n → GaussianInt) (hz : ∀ i, Irreducible (z i))
    (hinj : Function.Injective z)
    (hstep : ∀ i j : Fin n, j.val = i.val + 1 → dist (z j : ℂ) (z i : ℂ) ≤ D) : n ≤ B := by
  classical
  cases n with
  | zero => exact Nat.zero_le _
  | succ n =>
    let f : Fin (n + 1) → PrimeVertex := fun i => ⟨z i, hz i⟩
    have hf : Function.Injective f := fun i j h => hinj (congrArg Subtype.val h)
    have hreach (i : Fin (n + 1)) : (primeGraph D).Reachable (f 0) (f i) := by
      induction i using Fin.induction with
      | zero => exact SimpleGraph.Reachable.refl _
      | succ i ih =>
        apply ih.trans
        apply SimpleGraph.Adj.reachable
        exact ⟨fun h => (by have hh := congrArg Fin.val (hf h); simp at hh),
          by simpa only [dist_comm] using hstep i.castSucc i.succ rfl⟩
    have hsubset : Set.range f ⊆ component D (f 0) := by
      rintro _ ⟨i, rfl⟩
      exact hreach i
    have hle := (Set.ncard_le_ncard hsubset (hB _).1).trans (hB _).2
    simpa only [Set.ncard_range_of_injective hf, Nat.card_fin] using hle

theorem endpoints_of_finiteSieve (hsieve : FiniteSieveEndpoint) : MainEndpoint ∧ UniformEndpoint := by
  refine ⟨main_of_finiteSieve hsieve, fun D => ?_⟩
  obtain ⟨B, hB⟩ := prime_components_of_finiteSieve hsieve D
  exact ⟨B, hB, finite_prime_walk_bound hB⟩

end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat

def PrimitiveDirection (v : GaussianInt) : Prop := IsCoprime v.re v.im

theorem int_multiple_of_determinant_zero {v w : GaussianInt}
    (hv : PrimitiveDirection v) (hvw : determinant v w = 0) :
    ∃ a : ℤ, w = (a : GaussianInt) * v := by
  obtain ⟨r, s, hrs⟩ := hv
  refine ⟨r * w.re + s * w.im, ?_⟩
  change v.re * w.im - v.im * w.re = 0 at hvw
  ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast,
    Zsqrtd.im_intCast, zero_mul, mul_zero, add_zero]
  · linarith [congrArg (fun x : ℤ => x * w.re) hrs,
      congrArg (fun x : ℤ => s * x) hvw]
  · linarith [congrArg (fun x : ℤ => x * w.im) hrs,
      congrArg (fun x : ℤ => r * x) hvw]

theorem exists_primitive_direction {w : GaussianInt} (hw : w ≠ 0) :
    ∃ v : GaussianInt, PrimitiveDirection v ∧ v ≠ 0 ∧
      ∃ a : ℤ, a ≠ 0 ∧ w = (a : GaussianInt) * v := by
  have hg := (Zsqrtd.gcd_pos_iff w).mpr hw
  obtain ⟨v, hv, hcop⟩ := Zsqrtd.exists_coprime_of_gcd_pos hg
  refine ⟨v, hcop, ?_, (Int.gcd w.re w.im : ℤ), by exact_mod_cast hg.ne', hv⟩
  intro h
  apply hw
  simp only [h, mul_zero] at hv
  exact hv

theorem norm_dvd_norm {a b : GaussianInt} (h : a ∣ b) : a.norm ∣ b.norm := by
  obtain ⟨u, rfl⟩ := h
  rw [Zsqrtd.norm_mul]
  exact dvd_mul_right _ _

theorem factor_dvd_integer_iff {p : ℕ} {π : GaussianInt} (hp : Nat.Prime p)
    (hπ : π.norm = (p : ℤ)) (a : ℤ) : π ∣ (a : GaussianInt) ↔ (p : ℤ) ∣ a := by
  have hp' : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  constructor
  · intro h
    have hn := norm_dvd_norm h
    rw [hπ, Zsqrtd.norm_intCast] at hn
    exact (hp'.dvd_mul.mp hn).elim id id
  · intro h
    have hd : π ∣ (p : GaussianInt) := by
      have he : (p : GaussianInt) = π * star π := by
        rw [← Zsqrtd.norm_eq_mul_conj, hπ]
        simp
      rw [he]
      exact dvd_mul_right _ _
    exact hd.trans (map_dvd (Int.castRingHom GaussianInt) h)

theorem not_both_factors_dvd_primitive {p : ℕ} {π v : GaussianInt}
    (hp : Nat.Prime p) (hpodd : p ≠ 2) (hπ : π.norm = (p : ℤ))
    (hv : PrimitiveDirection v) : ¬ (π ∣ v ∧ star π ∣ v) := by
  rintro ⟨h1, h2⟩
  have hs : π ∣ star v := by
    obtain ⟨u, hu⟩ := h2
    refine ⟨star u, ?_⟩
    simpa only [star_mul, star_star, mul_comm] using congrArg star hu
  have hreal : π ∣ ((2 * v.re : ℤ) : GaussianInt) := by
    have heq : ((2 * v.re : ℤ) : GaussianInt) = v + star v := by
      ext <;> simp
      ring
    rw [heq]
    exact dvd_add h1 hs
  have himag : π ∣ ((2 * v.im : ℤ) : GaussianInt) := by
    have heq : ((2 * v.im : ℤ) : GaussianInt) =
        (⟨0, -1⟩ : GaussianInt) * (v - star v) := by
      ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
      ring
    rw [heq]
    exact dvd_mul_of_dvd_right (dvd_sub h1 hs) _
  have hp' : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hp2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have hn : p ∣ 2 := by exact_mod_cast h
    have hh := (Nat.dvd_prime Nat.prime_two).mp hn
    exact hh.elim hp.ne_one hpodd
  have hr : (p : ℤ) ∣ v.re :=
    (hp'.dvd_mul.mp ((factor_dvd_integer_iff hp hπ _).mp hreal)).resolve_left hp2
  have hi : (p : ℤ) ∣ v.im :=
    (hp'.dvd_mul.mp ((factor_dvd_integer_iff hp hπ _).mp himag)).resolve_left hp2
  exact hp'.not_isUnit (hv.isUnit_of_dvd' hr hi)

def signedFactor (π : GaussianInt) (b : Bool) : GaussianInt := if b then π else star π

theorem signedFactor_norm (π : GaussianInt) (b : Bool) : (signedFactor π b).norm = π.norm := by
  cases b <;> simp [signedFactor, Zsqrtd.norm_conj]

theorem signedFactor_irreducible {π : GaussianInt} (hπ : Irreducible π) (b : Bool) :
    Irreducible (signedFactor π b) := by
  cases b
  · exact (MulEquiv.irreducible_iff (starRingAut : RingAut GaussianInt)).mpr hπ
  · exact hπ

theorem coprime_factors_of_norm_primes {p q : ℕ} {π ρ : GaussianInt}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hπ : π.norm = (p : ℤ)) (hρ : ρ.norm = (q : ℤ)) : IsCoprime π ρ := by
  have hc : Nat.Coprime p q := (hp.coprime_iff_not_dvd).mpr (by
    intro hd
    have hh := (Nat.dvd_prime hq).mp hd
    exact hh.elim hp.ne_one hpq)
  have hcz : IsCoprime (p : ℤ) (q : ℤ) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    simpa using hc
  have hcg := hcz.map (Int.castRingHom GaussianInt)
  have hdπ : π ∣ (p : GaussianInt) := (factor_dvd_integer_iff hp hπ _).mpr (dvd_refl _)
  have hdρ : ρ ∣ (q : GaussianInt) := (factor_dvd_integer_iff hq hρ _).mpr (dvd_refl _)
  exact hcg.of_isCoprime_of_dvd_left hdπ |>.of_isCoprime_of_dvd_right hdρ

theorem norm_finset_prod {ι : Type uIota} (s : Finset ι) (f : ι → GaussianInt) :
    (∏ i ∈ s, f i).norm = ∏ i ∈ s, (f i).norm := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, Zsqrtd.norm_mul, ih]

theorem SplitSieve.prod_factors_dvd (s : SplitSieve) (t : Finset ℕ) (ht : t ⊆ s.primes)
    (σ : ℕ → Bool) {v : GaussianInt}
    (hd : ∀ p ∈ t, signedFactor (s.factor p) (σ p) ∣ v) :
    (∏ p ∈ t, signedFactor (s.factor p) (σ p)) ∣ v := by
  apply Finset.prod_dvd_of_coprime _ hd
  intro p hp q hq hpq
  exact coprime_factors_of_norm_primes (s.prime_mem p (ht hp)) (s.prime_mem q (ht hq)) hpq
    ((signedFactor_norm _ _).trans (s.factor_norm p (ht hp)))
    ((signedFactor_norm _ _).trans (s.factor_norm q (ht hq)))

theorem SplitSieve.eligible_product_le_norm (s : SplitSieve) (t : Finset ℕ)
    (ht : t ⊆ s.primes) (σ : ℕ → Bool) {v : GaussianInt} (hv : v ≠ 0)
    (hd : ∀ p ∈ t, signedFactor (s.factor p) (σ p) ∣ v) :
    (∏ p ∈ t, (p : ℤ)) ≤ v.norm := by
  have hle := norm_le_of_dvd hv (s.prod_factors_dvd t ht σ hd)
  rw [norm_finset_prod] at hle
  convert hle using 1
  apply Finset.prod_congr rfl
  intro p hp
  exact ((signedFactor_norm _ _).trans (s.factor_norm p (ht hp))).symm

open scoped Classical in

theorem SplitSieve.uneligible_product_dvd_coefficient (s : SplitSieve)
    (t : Finset ℕ) (ht : t ⊆ s.primes) (σ : ℕ → Bool) (v : GaussianInt) (a : ℤ)
    (hw : (∏ p ∈ t, signedFactor (s.factor p) (σ p)) ∣ (a : GaussianInt) * v) :
    (∏ p ∈ t.filter (fun p => ¬ signedFactor (s.factor p) (σ p) ∣ v), (p : ℤ)) ∣ a := by
  classical
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    have hp' := s.prime_mem p (ht (Finset.mem_filter.mp hp).1)
    have hq' := s.prime_mem q (ht (Finset.mem_filter.mp hq).1)
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    change Nat.Coprime p q
    exact (hp'.coprime_iff_not_dvd).mpr (fun h =>
      ((Nat.dvd_prime hq').mp h).elim hp'.ne_one hpq)
  · intro p hp
    obtain ⟨hpt, hpv⟩ := Finset.mem_filter.mp hp
    have hpp := ht hpt
    have hd : signedFactor (s.factor p) (σ p) ∣ (a : GaussianInt) * v :=
      (Finset.dvd_prod_of_mem _ hpt).trans hw
    have ha := ((signedFactor_irreducible (s.factor_irreducible p hpp) (σ p)).prime.dvd_mul.mp hd).resolve_right hpv
    exact (factor_dvd_integer_iff (s.prime_mem p hpp)
      ((signedFactor_norm _ _).trans (s.factor_norm p hpp)) a).mp ha

open scoped Classical in

theorem SplitSieve.line_witness_norm_lower (s : SplitSieve)
    (t : Finset ℕ) (ht : t ⊆ s.primes) (σ : ℕ → Bool)
    {v w : GaussianInt} (hv : PrimitiveDirection v) (hw : w ≠ 0)
    (hline : determinant v w = 0)
    (hdiv : (∏ p ∈ t, signedFactor (s.factor p) (σ p)) ∣ w) :
    v.norm * (∏ p ∈ t.filter (fun p => ¬ signedFactor (s.factor p) (σ p) ∣ v), (p : ℤ)) ^ 2
      ≤ w.norm := by
  classical
  obtain ⟨a, rfl⟩ := int_multiple_of_determinant_zero hv hline
  have ha : a ≠ 0 := by intro h; simp [h] at hw
  have hd := s.uneligible_product_dvd_coefficient t ht σ v a hdiv
  have habs : 0 < |a| := abs_pos.mpr ha
  have hle := Int.le_of_dvd habs ((dvd_abs _ _).mpr hd)
  have hprod : 0 ≤ ∏ p ∈ t.filter (fun p => ¬ signedFactor (s.factor p) (σ p) ∣ v), (p : ℤ) :=
    Finset.prod_nonneg (fun _ _ => Int.natCast_nonneg _)
  have hs : (∏ p ∈ t.filter (fun p => ¬ signedFactor (s.factor p) (σ p) ∣ v), (p : ℤ)) ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_abs a]
  rw [Zsqrtd.norm_mul, Zsqrtd.norm_intCast]
  linarith [mul_le_mul_of_nonneg_left hs (GaussianInt.norm_nonneg v)]

end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat

open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable def fairCoin : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
instance fairCoin_probability : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance
noncomputable def signMeasure (ι : Type uIota) [Fintype ι] : Measure (ι → Bool) :=
  Measure.pi (fun _ => fairCoin)
instance signMeasure_probability (ι : Type uIota) [Fintype ι] : IsProbabilityMeasure (signMeasure ι) := by
  unfold signMeasure
  infer_instance

theorem fairCoin_mean (f : Bool → ℝ) : ∫ b, f b ∂fairCoin = (f false + f true) / 2 := by
  have hf : Integrable f fairCoin := Integrable.of_mem_Icc
    (min (f false) (f true)) (max (f false) (f true)) (by fun_prop) (by
      apply ae_of_all
      intro b
      cases b <;> simp)
  rw [integral_fintype hf]
  simp [fairCoin, measureReal_def,
    PMF.uniformOfFintype_apply]
  ring

theorem sign_hoeffding {ι : Type uIota} [Fintype ι] (f : ι → Bool → ℝ) (w : ι → ℝ)
    (hf : ∀ i b, f i b ∈ Set.Icc 0 (w i)) {ε : ℝ} (hε : 0 ≤ ε) :
    (signMeasure ι).real {σ | ε + ∑ i, (f i false + f i true) / 2 ≤ ∑ i, f i (σ i)}
      ≤ Real.exp (-ε ^ 2 / (2 * ∑ i, (((‖w i‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) := by
  classical
  let X : ι → (ι → Bool) → ℝ := fun i σ => f i (σ i) - (f i false + f i true) / 2
  have hsub (i : ι) : HasSubgaussianMGF (X i) ((‖w i‖₊ / 2) ^ 2) (signMeasure ι) := by
    have h := hasSubgaussianMGF_of_mem_Icc (μ := fairCoin) (X := f i)
      (by fun_prop) (ae_of_all _ (hf i))
    rw [fairCoin_mean] at h
    simp only [sub_zero] at h
    have he := (measurePreserving_eval (fun _ : ι => fairCoin) i).map_eq
    rw [← he] at h
    have heval : AEMeasurable (Function.eval i : (ι → Bool) → Bool) (signMeasure ι) :=
      (measurable_pi_apply i).aemeasurable
    exact HasSubgaussianMGF.of_map heval h
  have hind : iIndepFun X (signMeasure ι) :=
    iIndepFun_pi (X := fun i b => f i b - (f i false + f i true) / 2) (fun _ => by fun_prop)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := Finset.univ) (fun i _ => hsub i) hε
  simpa only [X, Finset.sum_sub_distrib, le_sub_iff_add_le, NNReal.coe_sum] using h

open scoped Classical in

noncomputable def SplitSieve.eligible (s : SplitSieve) (v : GaussianInt) : Finset ℕ :=
  s.primes.filter (fun p => s.factor p ∣ v ∨ star (s.factor p) ∣ v)

noncomputable def SplitSieve.lineLog (s : SplitSieve) (v : GaussianInt) (p : ℕ) (b : Bool) : ℝ := by
  classical
  exact if signedFactor (s.factor p) b ∣ v then Real.log p else 0

theorem SplitSieve.eligible_log_bound (s : SplitSieve) {v : GaussianInt} (hv : v ≠ 0) :
    ∑ p ∈ s.eligible v, Real.log (p : ℝ) ≤ Real.log (v.norm : ℝ) := by
  classical
  let σ : ℕ → Bool := fun p => decide (s.factor p ∣ v)
  have hnorm := s.eligible_product_le_norm (s.eligible v)
    (Finset.filter_subset _ _) σ hv (by
      intro p hp
      obtain ⟨_, hleft | hright⟩ := Finset.mem_filter.mp hp
      · simp [σ, signedFactor, hleft]
      · by_cases hd : s.factor p ∣ v
        · simp [σ, signedFactor, hd]
        · simpa [σ, signedFactor, hd] using hright)
  have hnorm' : ∏ p ∈ s.eligible v, (p : ℝ) ≤ (v.norm : ℝ) := by
    have h : ((∏ p ∈ s.eligible v, (p : ℤ)) : ℝ) ≤ (v.norm : ℝ) := by exact_mod_cast hnorm
    push_cast at h
    exact h
  have hpos (p : ℕ) (hp : p ∈ s.eligible v) : 0 < (p : ℝ) := by
    exact_mod_cast (s.prime_mem p (Finset.mem_filter.mp hp).1).pos
  have hlog := Real.log_le_log (Finset.prod_pos hpos) hnorm'
  rw [Real.log_prod (fun p hp => (hpos p hp).ne')] at hlog
  exact hlog

theorem SplitSieve.lineLog_mean (s : SplitSieve) {v : GaussianInt}
    (hv : PrimitiveDirection v) (hv0 : v ≠ 0) :
    ∑ p : s.primes, (s.lineLog v p false + s.lineLog v p true) / 2 ≤
      Real.log (v.norm : ℝ) / 2 := by
  classical
  have heq : ∑ p : s.primes, (s.lineLog v p false + s.lineLog v p true) =
      ∑ p ∈ s.eligible v, Real.log (p : ℝ) := by
    rw [Finset.sum_coe_sort s.primes (fun p => s.lineLog v p false + s.lineLog v p true),
      SplitSieve.eligible, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    have hp2 : p ≠ 2 := by have hm := s.mod_four p hp; omega
    have hnot := not_both_factors_dvd_primitive (s.prime_mem p hp) hp2 (s.factor_norm p hp) hv
    by_cases h1 : s.factor p ∣ v <;> by_cases h2 : star (s.factor p) ∣ v
    · exact False.elim (hnot ⟨h1,h2⟩)
    all_goals simp [SplitSieve.lineLog, signedFactor, h1, h2]
  rw [← Finset.sum_div, heq]
  exact div_le_div_of_nonneg_right (s.eligible_log_bound hv0) (by norm_num)

theorem SplitSieve.lineLog_tail (s : SplitSieve) {v : GaussianInt}
    (hv : PrimitiveDirection v) (hv0 : v ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) :
    (signMeasure s.primes).real {σ |
      Real.log (v.norm : ℝ) / 2 + ε ≤ ∑ p : s.primes, s.lineLog v p (σ p)}
    ≤ Real.exp (-ε ^ 2 / (2 * ∑ p : s.primes,
      (((‖Real.log (p : ℝ)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) := by
  classical
  apply le_trans (measureReal_mono (s₂ := {σ |
    ε + ∑ p : s.primes, (s.lineLog v p false + s.lineLog v p true) / 2 ≤
      ∑ p : s.primes, s.lineLog v p (σ p)}) ?_)
  · apply sign_hoeffding (fun p : s.primes => s.lineLog v p) (fun p => Real.log (p : ℝ))
    · intro p b
      have hp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by
        exact_mod_cast (s.prime_mem p p.property).one_lt.le)
      unfold SplitSieve.lineLog
      split_ifs
      · exact ⟨hp, le_rfl⟩
      · exact ⟨le_rfl, hp⟩
    · exact hε
  · intro σ hσ
    have hmean := s.lineLog_mean hv hv0
    change Real.log (v.norm : ℝ) / 2 + ε ≤ _ at hσ
    change ε + _ ≤ _
    linarith

end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat
open MeasureTheory ProbabilityTheory
open scoped NNReal

@[reducible] def Cube : ℕ → Type
  | 0 => Unit
  | n + 1 => Bool × Cube n
instance cubeFintype : (n : ℕ) → Fintype (Cube n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => @instFintypeProd Bool (Cube n) inferInstance (cubeFintype n)
instance cubeDecidableEq : (n : ℕ) → DecidableEq (Cube n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n + 1 => @instDecidableEqProd Bool (Cube n) inferInstance (cubeDecidableEq n)
def cubeDist : (n : ℕ) → Cube n → Cube n → ℕ
  | 0, _, _ => 0
  | n + 1, (b,x), (c,y) => (if b = c then 0 else 1) + cubeDist n x y
@[simp] theorem cubeDist_self (n : ℕ) (x : Cube n) : cubeDist n x x = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => obtain ⟨b,x⟩ := x; simp [cubeDist, ih]
@[simp] theorem cubeDist_zero_iff (n : ℕ) (x y : Cube n) : cubeDist n x y = 0 ↔ x = y := by
  induction n with
  | zero => simp only [cubeDist]
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    obtain ⟨c,y⟩ := y
    by_cases h : b = c <;> simp [cubeDist, h, ih, Prod.mk.injEq]
theorem cubeDist_symm (n : ℕ) (x y : Cube n) : cubeDist n x y = cubeDist n y x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    obtain ⟨c,y⟩ := y
    simp [cubeDist, eq_comm (a := b) (b := c), ih x y]
theorem cubeDist_triangle (n : ℕ) (x y z : Cube n) :
    cubeDist n x z ≤ cubeDist n x y + cubeDist n y z := by
  induction n with
  | zero => simp [cubeDist]
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    obtain ⟨c,y⟩ := y
    obtain ⟨d,z⟩ := z
    have h := ih x y z
    cases b <;> cases c <;> cases d <;> simp [cubeDist] <;> omega

noncomputable def cubeSize {n : ℕ} (S : Cube n → Prop) : ℕ := by
  classical
  exact ∑ x, if S x then 1 else 0
noncomputable def cubeBoundary {n : ℕ} (S : Cube n → Prop) : ℕ := by
  classical
  exact ∑ x, ∑ y, if S x ∧ ¬ S y ∧ cubeDist n x y = 1 then 1 else 0
noncomputable def cubeCross {n : ℕ} (A B : Cube n → Prop) : ℕ := by
  classical
  exact ∑ x, if A x ∧ ¬ B x then 1 else 0

theorem cubeSize_succ {n : ℕ} (S : Cube (n+1) → Prop) :
    cubeSize S = cubeSize (fun x => S (false,x)) + cubeSize (fun x => S (true,x)) := by
  classical
  simp only [cubeSize, Fintype.sum_prod_type, Fintype.sum_bool]
  ac_rfl

theorem cubeBoundary_succ {n : ℕ} (S : Cube (n+1) → Prop) :
    cubeBoundary S = cubeBoundary (fun x => S (false,x)) + cubeBoundary (fun x => S (true,x)) +
      cubeCross (fun x => S (false,x)) (fun x => S (true,x)) +
      cubeCross (fun x => S (true,x)) (fun x => S (false,x)) := by
  classical
  simp only [cubeBoundary, cubeCross, Fintype.sum_prod_type, Fintype.sum_bool, cubeDist,
    Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, zero_add, Nat.add_eq_left,
    cubeDist_zero_iff, Finset.sum_add_distrib]
  simp only [and_assoc, and_left_comm, and_comm, ite_and, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  omega

theorem cubeCross_card_le {n : ℕ} (A B : Cube n → Prop) : cubeSize A ≤ cubeSize B + cubeCross A B := by
  classical
  rw [cubeSize, cubeSize, cubeCross, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases ha : A x <;> by_cases hb : B x <;> simp [ha, hb]

theorem cube_degree (n : ℕ) (x : Cube n) : (∑ y, if cubeDist n x y = 1 then 1 else 0) = n := by
  classical
  induction n with
  | zero => simp [cubeDist]
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    cases b <;> simp only [Fintype.sum_prod_type, Fintype.sum_bool, cubeDist,
      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, zero_add, Nat.add_eq_left,
      cubeDist_zero_iff, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ih]
    omega

theorem binEntropy_ge_two_mul {p : ℝ} (hp0 : 0 ≤ p) (hp2 : p ≤ 1/2) :
    2 * p * Real.log 2 ≤ Real.binEntropy p := by
  have hc : ConcaveOn ℝ (Set.Icc 0 1) Real.binEntropy := Real.strictConcave_binEntropy.concaveOn
  have h := hc.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (2 : ℝ)⁻¹ ∈ Set.Icc 0 1 by norm_num)
    (show 0 ≤ 1 - 2*p by linarith) (show 0 ≤ 2*p by positivity) (by ring)
  simpa only [smul_eq_mul, Real.binEntropy_zero, Real.binEntropy_two_inv,
    mul_zero, zero_add, show 2*p*(2:ℝ)⁻¹ = p by ring] using h

theorem entropy_merge_of_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    2 * a * Real.log 2 ≤ (a+b)*Real.log (a+b) - a*Real.log a - b*Real.log b := by
  by_cases ha0 : a = 0
  · simp [ha0]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbp : 0 < b := hap.trans_le hab
  have ht : 0 < a+b := by positivity
  have hp0 : 0 ≤ a/(a+b) := by positivity
  have hp2 : a/(a+b) ≤ 1/2 := (div_le_iff₀ ht).mpr (by linarith)
  have h := mul_le_mul_of_nonneg_left (binEntropy_ge_two_mul hp0 hp2) ht.le
  have heq : (a+b) * Real.binEntropy (a/(a+b)) =
      (a+b)*Real.log (a+b) - a*Real.log a - b*Real.log b := by
    have hsub : 1-a/(a+b) = b/(a+b) := by field_simp; ring
    rw [Real.binEntropy, hsub, Real.log_inv, Real.log_inv,
      Real.log_div hap.ne' ht.ne', Real.log_div hbp.ne' ht.ne']
    field_simp
    ring
  rw [heq] at h
  have heq' : (a+b) * (2 * (a/(a+b)) * Real.log 2) = 2*a*Real.log 2 := by
    field_simp
  rwa [heq'] at h

theorem entropy_merge {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * min a b * Real.log 2 ≤ (a+b)*Real.log (a+b) - a*Real.log a - b*Real.log b := by
  rcases le_total a b with hab | hba
  · simpa [min_eq_left hab] using entropy_merge_of_le ha hab
  · have h := entropy_merge_of_le hb hba
    rw [min_eq_right hba]
    convert h using 1
    rw [add_comm b a]
    ring

theorem cube_edge_isoperimetric (n : ℕ) (S : Cube n → Prop) :
    (cubeSize S : ℝ) * ((n : ℝ) * Real.log 2 - Real.log (cubeSize S)) ≤
      (cubeBoundary S : ℝ) * Real.log 2 := by
  classical
  induction n with
  | zero =>
    by_cases hs : S () <;> simp [cubeSize, cubeBoundary, cubeDist, hs]
  | succ n ih =>
    have h0 := ih (fun x => S (false,x))
    have h1 := ih (fun x => S (true,x))
    have hac := cubeCross_card_le (fun x => S (false,x)) (fun x => S (true,x))
    have hbc := cubeCross_card_le (fun x => S (true,x)) (fun x => S (false,x))
    have hac' : (cubeSize (fun x => S (false,x)) : ℝ) ≤
        cubeSize (fun x => S (true,x)) + cubeCross (fun x => S (false,x)) (fun x => S (true,x)) := by
      exact_mod_cast hac
    have hbc' : (cubeSize (fun x => S (true,x)) : ℝ) ≤
        cubeSize (fun x => S (false,x)) + cubeCross (fun x => S (true,x)) (fun x => S (false,x)) := by
      exact_mod_cast hbc
    have he := entropy_merge (a := (cubeSize (fun x => S (false,x)) : ℝ))
      (b := (cubeSize (fun x => S (true,x)) : ℝ)) (by positivity) (by positivity)
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [cubeSize_succ, cubeBoundary_succ]
    push_cast
    rcases le_total (cubeSize (fun x => S (false,x)) : ℝ) (cubeSize (fun x => S (true,x)) : ℝ) with hab | hba
    · rw [min_eq_left hab] at he
      have hn : (0 : ℝ) ≤ cubeCross (fun x => S (false,x)) (fun x => S (true,x)) := by positivity
      nlinarith
    · rw [min_eq_right hba] at he
      have hn : (0 : ℝ) ≤ cubeCross (fun x => S (true,x)) (fun x => S (false,x)) := by positivity
      nlinarith

def cubeExpand {n : ℕ} (S : Cube n → Prop) (y : Cube n) : Prop :=
  S y ∨ ∃ x, S x ∧ cubeDist n x y = 1

def cubeExpandIter {n : ℕ} (S : Cube n → Prop) : ℕ → Cube n → Prop
  | 0 => S
  | h+1 => cubeExpand (cubeExpandIter S h)

theorem cubeSize_mono {n : ℕ} {S T : Cube n → Prop} (h : ∀ x, S x → T x) :
    cubeSize S ≤ cubeSize T := by
  classical
  apply Finset.sum_le_sum
  intro x _
  by_cases hs : S x
  · simp [hs, h x hs]
  · simp [hs]

theorem cube_card (n : ℕ) : Fintype.card (Cube n) = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Bool × Cube n) = _
    rw [Fintype.card_prod, Fintype.card_bool, ih, pow_succ]
    omega

theorem cubeSize_le (n : ℕ) (S : Cube n → Prop) : cubeSize S ≤ 2^n := by
  classical
  calc
    cubeSize S ≤ ∑ _ : Cube n, 1 := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs <;> omega
    _ = 2^n := by simp [cube_card]

theorem cubeBoundary_expand_bound {n : ℕ} (S : Cube n → Prop) :
    cubeBoundary S + n * cubeSize S ≤ n * cubeSize (cubeExpand S) := by
  classical
  have hdegree (y : Cube n) :
      (∑ x, if S x ∧ ¬ S y ∧ cubeDist n x y = 1 then 1 else 0) ≤
        n * (if ¬S y ∧ (∃ x, S x ∧ cubeDist n x y = 1) then 1 else 0) := by
    by_cases hy : ¬S y ∧ (∃ x, S x ∧ cubeDist n x y = 1)
    · rw [ite_eq_left hy, mul_one]
      calc
        _ ≤ ∑ x, if cubeDist n y x = 1 then 1 else 0 := by
          apply Finset.sum_le_sum
          intro x _
          by_cases h : S x ∧ ¬ S y ∧ cubeDist n x y = 1
          · simp [h, cubeDist_symm n y x]
          · simp [h]
        _ = n := cube_degree n y
    · simp only [hy, ↓reduceIte, mul_zero, Nat.le_zero]
      apply Finset.sum_eq_zero
      intro x _
      have hnot : ¬(S x ∧ ¬S y ∧ cubeDist n x y = 1) := by
        rintro ⟨hs, hns, hd⟩
        exact hy ⟨hns,x,hs,hd⟩
      simp [hnot]
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hdegree y)
  rw [← Finset.mul_sum] at hb
  have heq : cubeSize (cubeExpand S) = cubeSize S +
      ∑ y, if ¬S y ∧ (∃ x, S x ∧ cubeDist n x y = 1) then 1 else 0 := by
    rw [cubeSize, cubeSize, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hs : S y <;> simp [cubeExpand, hs]
  unfold cubeBoundary
  rw [Finset.sum_comm, heq, Nat.mul_add]
  omega

theorem cubeExpandIter_witness {n h : ℕ} {S : Cube n → Prop} {x : Cube n}
    (hx : cubeExpandIter S h x) : ∃ y, S y ∧ cubeDist n y x ≤ h := by
  induction h generalizing x with
  | zero => exact ⟨x,hx,by simp⟩
  | succ h ih =>
    rcases hx with hx | ⟨z,hz,hzx⟩
    · obtain ⟨y,hy,hyx⟩ := ih hx
      exact ⟨y,hy,by omega⟩
    · obtain ⟨y,hy,hyz⟩ := ih hz
      exact ⟨y,hy,by have ht := cubeDist_triangle n y z x; omega⟩

theorem cubeExpandIter_disjoint {n h : ℕ} {S T : Cube n → Prop}
    (hsep : ∀ x, S x → ∀ y, T y → 2*h < cubeDist n x y) :
    ∀ x, ¬(cubeExpandIter S h x ∧ cubeExpandIter T h x) := by
  rintro x ⟨hs,ht⟩
  obtain ⟨y,hy,hyx⟩ := cubeExpandIter_witness hs
  obtain ⟨z,hz,hzx⟩ := cubeExpandIter_witness ht
  have h := hsep y hy z hz
  have htri := cubeDist_triangle n y x z
  rw [cubeDist_symm n x z] at htri
  omega

theorem cubeSize_sum_le {n : ℕ} {ι : Type uIota} [Fintype ι] (S : ι → Cube n → Prop)
    (hd : ∀ i j, i ≠ j → ∀ x, ¬(S i x ∧ S j x)) :
    ∑ i, cubeSize (S i) ≤ 2^n := by
  classical
  unfold cubeSize
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _ : Cube n, 1 := by
      apply Finset.sum_le_sum
      intro x _
      by_cases he : ∃ i, S i x
      · obtain ⟨i,hi⟩ := he
        rw [Finset.sum_eq_single i]
        · simp [hi]
        · intro j _ hji
          have hnot : ¬S j x := fun hj => hd j i hji x ⟨hj,hi⟩
          simp [hnot]
        · simp
      · have hh : ∀ i, ¬S i x := by simpa only [not_exists] using he
        simp [hh]
    _ = 2^n := by simp [cube_card]

theorem cube_growth {n : ℕ} (hn : 0 < n) (S : Cube n → Prop) {a E : ℝ}
    (hE : 0 < E) (hlogE : Real.log E ≤ (n : ℝ) * Real.log 2 - a)
    (hsize : (cubeSize S : ℝ) ≤ E) :
    (1 + a / ((n : ℝ) * Real.log 2)) * cubeSize S ≤ cubeSize (cubeExpand S) := by
  by_cases hz : cubeSize S = 0
  · simp [hz]
  have hpos : (0 : ℝ) < cubeSize S := by exact_mod_cast Nat.pos_of_ne_zero hz
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < (n : ℝ) * Real.log 2 := mul_pos hnpos hlogtwo
  have hl := ((Real.log_le_log_iff hpos hE).mpr hsize).trans hlogE
  have hi := cube_edge_isoperimetric n S
  have hb : (cubeBoundary S : ℝ) + n * cubeSize S ≤ n * cubeSize (cubeExpand S) := by
    exact_mod_cast cubeBoundary_expand_bound S
  apply (mul_le_mul_iff_left₀ hden).mp
  field_simp at ⊢
  linarith [mul_le_mul_of_nonneg_left hl hpos.le,
    mul_le_mul_of_nonneg_right hb hlogtwo.le]

theorem cube_iter_growth {n : ℕ} (S : Cube n → Prop) {δ E : ℝ} (hδ : 0 ≤ δ)
    (hgrow : ∀ T : Cube n → Prop, (cubeSize T : ℝ) ≤ E →
      (1+δ)*cubeSize T ≤ cubeSize (cubeExpand T)) (h : ℕ) :
    min E ((1+δ)^h * cubeSize S) ≤ cubeSize (cubeExpandIter S h) := by
  induction h with
  | zero => simpa only [pow_zero, one_mul, cubeExpandIter] using
      (min_le_right E (cubeSize S : ℝ))
  | succ h ih =>
    have hmono : (cubeSize (cubeExpandIter S h) : ℝ) ≤ cubeSize (cubeExpandIter S (h+1)) := by
      exact_mod_cast cubeSize_mono (S := cubeExpandIter S h) (T := cubeExpand (cubeExpandIter S h))
        (fun _ hx => Or.inl hx)
    by_cases hlarge : E ≤ (cubeSize (cubeExpandIter S h) : ℝ)
    · exact (min_le_left _ _).trans (hlarge.trans hmono)
    · have hsmall : (cubeSize (cubeExpandIter S h) : ℝ) ≤ E := le_of_not_ge hlarge
      have hpow : (1+δ)^h * cubeSize S ≤ E := by
        by_contra hnot
        rw [min_eq_left (le_of_not_ge hnot)] at ih
        exact hlarge ih
      rw [min_eq_right hpow] at ih
      have hmul := mul_le_mul_of_nonneg_left ih (by linarith : 0 ≤ 1+δ)
      have hg := hgrow (cubeExpandIter S h) hsmall
      apply (min_le_right _ _).trans
      simpa only [pow_succ, mul_assoc, mul_left_comm, cubeExpandIter] using hmul.trans hg

theorem cube_separated_bound {n h : ℕ} (hn : 0 < n) {ι : Type uIota} [Fintype ι]
    (S : ι → Cube n → Prop) {a E A : ℝ} (ha : 0 ≤ a) (hE : 0 < E)
    (hlogE : Real.log E ≤ (n : ℝ) * Real.log 2 - a)
    (hseed : ∀ i, A * cubeSize (S i) ≤ E)
    (hfactor : A ≤ (1 + a / ((n : ℝ)*Real.log 2))^h)
    (hsep : ∀ i j, i ≠ j → ∀ x, S i x → ∀ y, S j y → 2*h < cubeDist n x y) :
    A * (∑ i, (cubeSize (S i) : ℝ)) ≤ (2 : ℝ)^n := by
  have hδ : 0 ≤ a / ((n : ℝ)*Real.log 2) := by
    apply div_nonneg ha
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  have hlarge (i : ι) : A * cubeSize (S i) ≤ cubeSize (cubeExpandIter (S i) h) := by
    apply le_trans (le_min (hseed i) (mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg _)))
    exact cube_iter_growth (S i) hδ (fun T ht => cube_growth hn T hE hlogE ht) h
  rw [Finset.mul_sum]
  apply (Finset.sum_le_sum (fun i _ => hlarge i)).trans
  have hd : ∀ i j, i ≠ j → ∀ x, ¬(cubeExpandIter (S i) h x ∧ cubeExpandIter (S j) h x) := by
    intro i j hij
    exact cubeExpandIter_disjoint (hsep i j hij)
  exact_mod_cast cubeSize_sum_le (fun i => cubeExpandIter (S i) h) hd

end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat
open MeasureTheory ProbabilityTheory
open scoped NNReal

def cubeEquiv : (n : ℕ) → Cube n ≃ (Fin n → Bool)
  | 0 => {
      toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => ()
      left_inv := fun x => by cases x; rfl
      right_inv := fun f => by funext i; exact Fin.elim0 i }
  | n+1 => (Equiv.prodCongr (Equiv.refl Bool) (cubeEquiv n)).trans (Fin.consEquiv (fun _ => Bool))

noncomputable def cubeSignEquiv (ι : Type uIota) [Fintype ι] : Cube (Fintype.card ι) ≃ (ι → Bool) :=
  (cubeEquiv (Fintype.card ι)).trans
    (Equiv.arrowCongr (Fintype.equivFin ι).symm (Equiv.refl Bool))

noncomputable def signDist {ι : Type uIota} [Fintype ι] (σ τ : ι → Bool) : ℕ := by
  classical
  exact ∑ i, if σ i = τ i then 0 else 1

theorem cubeEquiv_dist (n : ℕ) (x y : Cube n) :
    signDist (cubeEquiv n x) (cubeEquiv n y) = cubeDist n x y := by
  classical
  induction n with
  | zero => simp [signDist, cubeDist]
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    obtain ⟨c,y⟩ := y
    simp only [signDist, Fin.sum_univ_succ, cubeEquiv, Equiv.trans_apply,
      Equiv.prodCongr_apply, Fin.consEquiv_apply, Fin.cons_zero,
      Fin.cons_succ, cubeDist]
    congr 1
    exact ih x y

theorem cubeSignEquiv_dist (ι : Type uIota) [Fintype ι] (x y : Cube (Fintype.card ι)) :
    signDist (cubeSignEquiv ι x) (cubeSignEquiv ι y) = cubeDist (Fintype.card ι) x y := by
  classical
  rw [← cubeEquiv_dist]
  unfold signDist cubeSignEquiv
  simp only [Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.symm_symm]
  exact (Fintype.equivFin ι).sum_comp (fun i => if cubeEquiv (Fintype.card ι) x i =
    cubeEquiv (Fintype.card ι) y i then (0 : ℕ) else 1)

theorem signMeasure_real_singleton {ι : Type uIota} [Fintype ι] (σ : ι → Bool) :
    (signMeasure ι).real {σ} = ((2 : ℝ)^Fintype.card ι)⁻¹ := by
  simp [measureReal_def, signMeasure, Measure.pi_singleton, fairCoin,
    PMF.uniformOfFintype_apply]

open scoped Classical in

theorem signMeasure_real_set {ι : Type uIota} [Fintype ι] (S : Set (ι → Bool)) :
    (signMeasure ι).real S = (∑ σ, if σ ∈ S then (1 : ℝ) else 0) /
      (2 : ℝ)^Fintype.card ι := by
  classical
  have he : S = (↑(Finset.univ.filter (· ∈ S)) : Set (ι → Bool)) := by ext; simp
  conv_lhs => rw [he, ← sum_measureReal_singleton]
  rw [Finset.sum_filter, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hσ : σ ∈ S <;> simp [hσ, signMeasure_real_singleton]

theorem cubeSignEquiv_measure {ι : Type uIota} [Fintype ι] (S : (ι → Bool) → Prop) :
    (signMeasure ι).real {σ | S σ} =
      (cubeSize (fun x => S (cubeSignEquiv ι x)) : ℝ) / (2 : ℝ)^Fintype.card ι := by
  classical
  rw [signMeasure_real_set]
  congr 1
  simp only [Set.mem_ofPred_eq]
  rw [← (cubeSignEquiv ι).sum_comp (fun σ => if S σ then (1 : ℝ) else 0)]
  simp only [cubeSize, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

noncomputable def SplitSieve.extendSigns (s : SplitSieve) (σ : s.primes → Bool) (p : ℕ) : Bool := by
  classical
  exact if hp : p ∈ s.primes then σ ⟨p,hp⟩ else false

@[simp] theorem SplitSieve.extendSigns_mem (s : SplitSieve) (σ : s.primes → Bool)
    (p : ℕ) (hp : p ∈ s.primes) : s.extendSigns σ p = σ ⟨p,hp⟩ := by
  simp [SplitSieve.extendSigns, hp]

noncomputable def SplitSieve.signedProduct (s : SplitSieve) (σ : s.primes → Bool) : GaussianInt :=
  ∏ p ∈ s.primes, signedFactor (s.factor p) (s.extendSigns σ p)

theorem SplitSieve.line_witness_log_lower (s : SplitSieve) (σ : s.primes → Bool)
    {v w : GaussianInt} (hv : PrimitiveDirection v) (hv0 : v ≠ 0) (hw : w ≠ 0)
    (hline : determinant v w = 0) (hdiv : s.signedProduct σ ∣ w)
    {B : ℝ} (hbound : (w.norm : ℝ) ≤ B) :
    Real.log (v.norm : ℝ) / 2 + (∑ p : s.primes, Real.log (p : ℝ)) - Real.log B / 2 ≤
      ∑ p : s.primes, s.lineLog v p (σ p) := by
  classical
  let t := s.primes.filter (fun p => ¬signedFactor (s.factor p) (s.extendSigns σ p) ∣ v)
  have hp (p : ℕ) (hp : p ∈ t) : 0 < (p : ℝ) := by
    exact_mod_cast (s.prime_mem p (Finset.mem_filter.mp hp).1).pos
  have hprod : 0 < ∏ p ∈ t, (p : ℝ) := Finset.prod_pos hp
  have hvpos : 0 < (v.norm : ℝ) := by exact_mod_cast (GaussianInt.norm_pos.mpr hv0)
  have hlo := s.line_witness_norm_lower s.primes (fun _ h => h) (s.extendSigns σ) hv hw hline hdiv
  have hlow : (v.norm : ℝ) * (∏ p ∈ t, (p : ℝ))^2 ≤ B := by
    apply le_trans ?_ hbound
    have hc : ((v.norm * (∏ p ∈ t, (p : ℤ))^2 : ℤ) : ℝ) ≤ (w.norm : ℝ) := by exact_mod_cast hlo
    push_cast at hc
    exact hc
  have hlog := Real.log_le_log (mul_pos hvpos (sq_pos_of_pos hprod)) hlow
  rw [Real.log_mul hvpos.ne' (sq_pos_of_pos hprod).ne', Real.log_pow,
    Real.log_prod (fun p hp' => (hp p hp').ne')] at hlog
  have hsum : (∑ p ∈ t, Real.log (p : ℝ)) =
      (∑ p : s.primes, Real.log (p : ℝ)) - ∑ p : s.primes, s.lineLog v p (σ p) := by
    calc
      _ = ∑ p ∈ s.primes, (Real.log (p : ℝ) - s.lineLog v p (s.extendSigns σ p)) := by
        unfold t
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro p hp'
        unfold SplitSieve.lineLog
        split_ifs <;> simp_all
      _ = _ := by
        rw [← Finset.sum_coe_sort s.primes
          (fun p => Real.log (p : ℝ) - s.lineLog v p (s.extendSigns σ p))]
        simp [SplitSieve.extendSigns, Finset.sum_sub_distrib]
  rw [hsum] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith only [hlog]

def SplitSieve.lineEvent (s : SplitSieve) (Q : Set GaussianInt) (v : GaussianInt)
    (σ : s.primes → Bool) : Prop :=
  ∃ w ∈ Q, w ≠ 0 ∧ determinant v w = 0 ∧ s.signedProduct σ ∣ w

theorem SplitSieve.line_event_tail (s : SplitSieve) {Q : Set GaussianInt}
    {v : GaussianInt} (hv : PrimitiveDirection v) (hv0 : v ≠ 0) {B ε : ℝ}
    (hQ : ∀ w ∈ Q, (w.norm : ℝ) ≤ B) (hε : 0 ≤ ε)
    (hexcess : ε ≤ (∑ p : s.primes, Real.log (p : ℝ)) - Real.log B / 2) :
    (signMeasure s.primes).real {σ | s.lineEvent Q v σ} ≤
      Real.exp (-ε^2 / (2 * ∑ p : s.primes,
        (((‖Real.log (p : ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ))) := by
  apply le_trans (measureReal_mono (s₂ := {σ |
    Real.log (v.norm : ℝ) / 2 + ε ≤ ∑ p : s.primes, s.lineLog v p (σ p)}) ?_)
  · exact s.lineLog_tail hv hv0 hε
  · rintro σ ⟨w,hwQ,hw,hline,hd⟩
    have hl := s.line_witness_log_lower σ hv hv0 hw hline hd (hQ w hwQ)
    change Real.log (v.norm : ℝ) / 2 + ε ≤ _
    linarith

open scoped Classical in

noncomputable def SplitSieve.commonProduct (s : SplitSieve) (σ τ : s.primes → Bool) : GaussianInt :=
  ∏ p ∈ s.primes.filter (fun p => s.extendSigns σ p = s.extendSigns τ p),
    signedFactor (s.factor p) (s.extendSigns σ p)

theorem SplitSieve.commonProduct_dvd_left (s : SplitSieve) (σ τ : s.primes → Bool) :
    s.commonProduct σ τ ∣ s.signedProduct σ := by
  classical
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

theorem SplitSieve.commonProduct_comm (s : SplitSieve) (σ τ : s.primes → Bool) :
    s.commonProduct σ τ = s.commonProduct τ σ := by
  classical
  unfold SplitSieve.commonProduct
  apply Finset.prod_congr
  · ext p
    simp only [Finset.mem_filter, eq_comm]
  · intro p hp
    rw [(Finset.mem_filter.mp hp).2]

theorem SplitSieve.commonProduct_dvd_right (s : SplitSieve) (σ τ : s.primes → Bool) :
    s.commonProduct σ τ ∣ s.signedProduct τ := by
  rw [s.commonProduct_comm]
  exact s.commonProduct_dvd_left τ σ

open scoped Classical in
theorem SplitSieve.signDist_eq_card (s : SplitSieve) (σ τ : s.primes → Bool) :
    signDist σ τ = (s.primes.filter (fun p => s.extendSigns σ p ≠ s.extendSigns τ p)).card := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.sum_coe_sort s.primes
    (fun p => if s.extendSigns σ p ≠ s.extendSigns τ p then 1 else 0)]
  unfold signDist
  apply Finset.sum_congr rfl
  intro p _
  simp [SplitSieve.extendSigns]

theorem SplitSieve.period_le_common_norm (s : SplitSieve) (σ τ : s.primes → Bool)
    {U : ℝ} (hpU : ∀ p ∈ s.primes, (p : ℝ) ≤ U) :
    (s.period : ℝ) ≤ ((s.commonProduct σ τ).norm : ℝ) * U^(signDist σ τ) := by
  classical
  let c := s.primes.filter (fun p => s.extendSigns σ p = s.extendSigns τ p)
  let d := s.primes.filter (fun p => s.extendSigns σ p ≠ s.extendSigns τ p)
  have hc : ((s.commonProduct σ τ).norm : ℝ) = ∏ p ∈ c, (p : ℝ) := by
    unfold SplitSieve.commonProduct
    rw [norm_finset_prod, Int.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    rw [signedFactor_norm, s.factor_norm p (Finset.mem_filter.mp hp).1]
    exact_mod_cast (rfl : (p : ℝ) = p)
  have hd : (∏ p ∈ d, (p : ℝ)) ≤ U^d.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun p _ => Nat.cast_nonneg p)
      (fun p hp => hpU p (Finset.mem_filter.mp hp).1)
  have hp : (s.period : ℝ) = (∏ p ∈ c, (p : ℝ)) * (∏ p ∈ d, (p : ℝ)) := by
    unfold SplitSieve.period
    push_cast
    exact (Finset.prod_filter_mul_prod_filter_not s.primes
      (fun p => s.extendSigns σ p = s.extendSigns τ p) (fun p => (p : ℝ))).symm
  rw [hp, hc, s.signDist_eq_card]
  exact mul_le_mul_of_nonneg_left hd (Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p))

theorem SplitSieve.near_witnesses_collinear (s : SplitSieve) (σ τ : s.primes → Bool)
    {w w' : GaussianInt} (hw : s.signedProduct σ ∣ w) (hw' : s.signedProduct τ ∣ w')
    {U B : ℝ} (hU : 0 < U) (hpU : ∀ p ∈ s.primes, (p : ℝ) ≤ U)
    (hdet : (|determinant w w'| : ℝ) ≤ B)
    (hsmall : B * U^(signDist σ τ) < (s.period : ℝ)) : determinant w w' = 0 := by
  have hbound := lt_of_lt_of_le hsmall (s.period_le_common_norm σ τ hpU)
  have hlt : B < ((s.commonProduct σ τ).norm : ℝ) :=
    (mul_lt_mul_iff_left₀ (pow_pos hU _)).mp (by simpa only [mul_comm] using hbound)
  apply determinant_eq_zero_of_common_factor
    ((s.commonProduct_dvd_left σ τ).trans hw) ((s.commonProduct_dvd_right σ τ).trans hw')
  exact_mod_cast hdet.trans_lt hlt

theorem determinant_zero_trans {u v w : GaussianInt} (hv : v ≠ 0)
    (huv : determinant u v = 0) (hvw : determinant v w = 0) :
    determinant u w = 0 := by
  have hcoord : v.re ≠ 0 ∨ v.im ≠ 0 := by
    contrapose! hv
    ext <;> simp [hv.1, hv.2]
  unfold determinant at *
  rcases hcoord with hr | hi
  · apply (mul_eq_zero.mp (show v.re * (u.re * w.im - u.im * w.re) = 0 by
      linarith [congrArg (fun x : ℤ => x * w.re) huv,
        congrArg (fun x : ℤ => u.re * x) hvw])).resolve_left hr
  · apply (mul_eq_zero.mp (show v.im * (u.re * w.im - u.im * w.re) = 0 by
      linarith [congrArg (fun x : ℤ => x * w.im) huv,
        congrArg (fun x : ℤ => u.im * x) hvw])).resolve_left hi

@[simp] theorem determinant_self (v : GaussianInt) : determinant v v = 0 := by
  unfold determinant
  ring

theorem determinant_swap (u v : GaussianInt) : determinant u v = -determinant v u := by
  unfold determinant
  ring

def witnessLine (v : GaussianInt) : Set GaussianInt := {w | determinant v w = 0}

theorem witnessLine_eq {v w : GaussianInt} (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : determinant v w = 0) : witnessLine v = witnessLine w := by
  ext u
  constructor
  · intro hu
    exact determinant_zero_trans hv (by rw [determinant_swap, hvw, neg_zero]) hu
  · exact determinant_zero_trans hw hvw

def SplitSieve.badSign (s : SplitSieve) (Q : Set GaussianInt) (σ : s.primes → Bool) : Prop :=
  ∃ w ∈ Q, w ≠ 0 ∧ s.signedProduct σ ∣ w

noncomputable def SplitSieve.badWitness (s : SplitSieve) (Q : Set GaussianInt)
    (σ : {σ : s.primes → Bool // s.badSign Q σ}) : GaussianInt := σ.property.choose

theorem SplitSieve.badWitness_spec (s : SplitSieve) (Q : Set GaussianInt)
    (σ : {σ : s.primes → Bool // s.badSign Q σ}) :
    s.badWitness Q σ ∈ Q ∧ s.badWitness Q σ ≠ 0 ∧ s.signedProduct σ.val ∣ s.badWitness Q σ :=
  σ.property.choose_spec

def SplitSieve.badLines (s : SplitSieve) (Q : Set GaussianInt) : Set (Set GaussianInt) :=
  Set.range (fun σ : {σ : s.primes → Bool // s.badSign Q σ} => witnessLine (s.badWitness Q σ))

instance SplitSieve.badLines_finite (s : SplitSieve) (Q : Set GaussianInt) :
    Finite (s.badLines Q) := by
  unfold SplitSieve.badLines
  infer_instance

theorem SplitSieve.badLine_primitive (s : SplitSieve) (Q : Set GaussianInt)
    (L : s.badLines Q) : ∃ v : GaussianInt, PrimitiveDirection v ∧ v ≠ 0 ∧ witnessLine v = L.val := by
  obtain ⟨σ, hσ⟩ := L.property
  have hw := s.badWitness_spec Q σ
  obtain ⟨v,hv,hv0,a,_hanz,ha⟩ := exists_primitive_direction hw.2.1
  refine ⟨v,hv,hv0, ?_⟩
  rw [← hσ]
  apply witnessLine_eq hv0 hw.2.1
  rw [ha]
  unfold determinant
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]
  ring

def SplitSieve.lineClass (s : SplitSieve) (Q : Set GaussianInt) (L : s.badLines Q)
    (σ : s.primes → Bool) : Prop :=
  ∃ hσ : s.badSign Q σ, witnessLine (s.badWitness Q ⟨σ,hσ⟩) = L.val

theorem SplitSieve.badSign_iff_class (s : SplitSieve) (Q : Set GaussianInt) (σ : s.primes → Bool) :
    s.badSign Q σ ↔ ∃ L : s.badLines Q, s.lineClass Q L σ := by
  constructor
  · intro hσ
    exact ⟨⟨witnessLine (s.badWitness Q ⟨σ,hσ⟩), ⟨⟨σ,hσ⟩,rfl⟩⟩, hσ, rfl⟩
  · rintro ⟨L,hσ,_⟩
    exact hσ

theorem SplitSieve.lineClass_subset_event (s : SplitSieve) (Q : Set GaussianInt)
    (L : s.badLines Q) {v : GaussianInt} (hvL : witnessLine v = L.val) :
    {σ | s.lineClass Q L σ} ⊆ {σ | s.lineEvent Q v σ} := by
  rintro σ ⟨hσ,hL⟩
  have hw := s.badWitness_spec Q ⟨σ,hσ⟩
  refine ⟨_,hw.1,hw.2.1,?_,hw.2.2⟩
  change s.badWitness Q ⟨σ,hσ⟩ ∈ witnessLine v
  rw [hvL, ← hL]
  exact determinant_self _

theorem SplitSieve.lineClasses_separated (s : SplitSieve) (Q : Set GaussianInt)
    {U B : ℝ} (hU : 1 ≤ U) (hpU : ∀ p ∈ s.primes, (p : ℝ) ≤ U)
    (hdet : ∀ w ∈ Q, ∀ w' ∈ Q, (|determinant w w'| : ℝ) ≤ B)
    {h : ℕ} (hsmall : B * U^(2*h) < (s.period : ℝ)) (hB : 0 ≤ B) :
    ∀ L L' : s.badLines Q, L ≠ L' → ∀ σ, s.lineClass Q L σ →
      ∀ τ, s.lineClass Q L' τ → 2*h < signDist σ τ := by
  intro L L' hLL σ ⟨hσ,hσL⟩ τ ⟨hτ,hτL⟩
  by_contra hn
  have hd : signDist σ τ ≤ 2*h := le_of_not_gt hn
  have hw := s.badWitness_spec Q ⟨σ,hσ⟩
  have hw' := s.badWitness_spec Q ⟨τ,hτ⟩
  have hsm : B * U^(signDist σ τ) < (s.period : ℝ) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hU hd) hB).trans_lt hsmall
  have hcol := s.near_witnesses_collinear σ τ hw.2.2 hw'.2.2 (by linarith) hpU
    (hdet _ hw.1 _ hw'.1) hsm
  apply hLL
  apply Subtype.ext
  rw [← hσL, ← hτL]
  exact witnessLine_eq hw.2.1 hw'.2.1 hcol

theorem cubeSize_exists_le_sum {n : ℕ} {ι : Type uIota} [Fintype ι]
    (S : ι → Cube n → Prop) : cubeSize (fun x => ∃ i, S i x) ≤ ∑ i, cubeSize (S i) := by
  classical
  unfold cubeSize
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : ∃ i, S i x
  · obtain ⟨i, hi⟩ := hx
    rw [ite_eq_left ⟨i,hi⟩]
    have h : (if S i x then 1 else 0) ≤ ∑ j : ι, if S j x then 1 else 0 :=
      Finset.single_le_sum (f := fun j => if S j x then (1 : ℕ) else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simpa only [ite_eq_left hi] using h
  · simp only [ite_eq_right hx]
    exact Nat.zero_le _

theorem SplitSieve.signed_region_bound (s : SplitSieve) (Q : Set GaussianInt)
    (hr : 0 < s.primes.card) {U B N ε a E A : ℝ} {h : ℕ}
    (hU : 1 ≤ U) (hpU : ∀ p ∈ s.primes, (p : ℝ) ≤ U)
    (hB : 0 ≤ B) (hdet : ∀ w ∈ Q, ∀ w' ∈ Q, (|determinant w w'| : ℝ) ≤ B)
    (hsmall : B * U^(2*h) < (s.period : ℝ))
    (hQ : ∀ w ∈ Q, (w.norm : ℝ) ≤ N) (hε : 0 ≤ ε)
    (hexcess : ε ≤ (∑ p : s.primes, Real.log (p : ℝ)) - Real.log N / 2)
    (ha : 0 ≤ a) (hE : 0 < E) (hA : 0 < A)
    (hlogE : Real.log E ≤ (s.primes.card : ℝ) * Real.log 2 - a)
    (hseed : A * Real.exp (-ε^2 / (2 * ∑ p : s.primes,
      (((‖Real.log (p : ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ))) * (2 : ℝ)^s.primes.card ≤ E)
    (hfactor : A ≤ (1 + a / ((s.primes.card : ℝ)*Real.log 2))^h) :
    (signMeasure s.primes).real {σ | s.badSign Q σ} ≤ A⁻¹ := by
  classical
  let : Fintype (s.badLines Q) := Fintype.ofFinite _
  let S : s.badLines Q → Cube (Fintype.card s.primes) → Prop :=
    fun L x => s.lineClass Q L (cubeSignEquiv s.primes x)
  have hcard : Fintype.card s.primes = s.primes.card := Fintype.card_coe _
  have hpow : 0 < (2 : ℝ)^Fintype.card s.primes := pow_pos (by norm_num) _
  have hseed' (L : s.badLines Q) : A * cubeSize (S L) ≤ E := by
    obtain ⟨v,hv,hv0,hvL⟩ := s.badLine_primitive Q L
    have hm := (measureReal_mono (s.lineClass_subset_event Q L hvL)).trans
      (s.line_event_tail hv hv0 hQ hε hexcess)
    rw [cubeSignEquiv_measure] at hm
    have hc : (cubeSize (S L) : ℝ) ≤ Real.exp (-ε^2 / (2 * ∑ p : s.primes,
        (((‖Real.log (p : ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ))) * (2 : ℝ)^Fintype.card s.primes :=
      (div_le_iff₀ hpow).mp hm
    have hh := mul_le_mul_of_nonneg_left hc hA.le
    exact hh.trans (by simpa only [hcard, mul_assoc] using hseed)
  have hsep : ∀ L L' : s.badLines Q, L ≠ L' → ∀ x, S L x → ∀ y, S L' y →
      2*h < cubeDist (Fintype.card s.primes) x y := by
    intro L L' hLL x hx y hy
    have hh := s.lineClasses_separated Q hU hpU hdet hsmall hB L L' hLL
      (cubeSignEquiv s.primes x) hx (cubeSignEquiv s.primes y) hy
    simpa only [cubeSignEquiv_dist] using hh
  have hpack := cube_separated_bound (n := Fintype.card s.primes) (h := h)
    (by simpa only [hcard] using hr) S ha hE (by simpa only [hcard] using hlogE)
    hseed' (by simpa only [hcard] using hfactor) hsep
  have hunion : (cubeSize (fun x => s.badSign Q (cubeSignEquiv s.primes x)) : ℝ) ≤
      ∑ L, (cubeSize (S L) : ℝ) := by
    have he : (fun x => s.badSign Q (cubeSignEquiv s.primes x)) = (fun x => ∃ L, S L x) := by
      funext x
      exact propext (s.badSign_iff_class Q _)
    rw [he]
    exact_mod_cast cubeSize_exists_le_sum S
  rw [cubeSignEquiv_measure, div_le_iff₀ hpow]
  have hh := (mul_le_mul_of_nonneg_left hunion hA.le).trans hpack
  calc
    _ ≤ (2 : ℝ)^Fintype.card s.primes / A := (le_div_iff₀ hA).mpr (by simpa only [mul_comm] using hh)
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

theorem SplitSieve.signed_region_exp_bound (s : SplitSieve) (Q : Set GaussianInt)
    (hr : 0 < s.primes.card) {U B N ε a b : ℝ} {h : ℕ}
    (hU : 1 ≤ U) (hpU : ∀ p ∈ s.primes, (p : ℝ) ≤ U)
    (hB : 0 ≤ B) (hdet : ∀ w ∈ Q, ∀ w' ∈ Q, (|determinant w w'| : ℝ) ≤ B)
    (hsmall : B * U^(2*h) < (s.period : ℝ))
    (hQ : ∀ w ∈ Q, (w.norm : ℝ) ≤ N) (hε : 0 ≤ ε)
    (hexcess : ε ≤ (∑ p : s.primes, Real.log (p : ℝ)) - Real.log N / 2)
    (ha : 0 ≤ a) (hb : b ≤ a)
    (htail : 2*a ≤ ε^2 / (2 * ∑ p : s.primes,
      (((‖Real.log (p : ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ)))
    (hgrowth : b ≤ (h : ℝ) * Real.log (1 + a / ((s.primes.card : ℝ)*Real.log 2))) :
    (signMeasure s.primes).real {σ | s.badSign Q σ} ≤ Real.exp (-b) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr' : 0 < (s.primes.card : ℝ) := by exact_mod_cast hr
  have hbase : 0 < 1 + a / ((s.primes.card : ℝ)*Real.log 2) := by
    have := div_nonneg ha (mul_pos hr' htwo).le
    linarith
  have hbexp : Real.exp b ≤ (1 + a / ((s.primes.card : ℝ)*Real.log 2))^h := by
    rw [← Real.exp_log (pow_pos hbase h)]
    apply Real.exp_le_exp.mpr
    simpa only [Real.log_pow] using hgrowth
  have hh := s.signed_region_bound Q hr hU hpU hB hdet hsmall hQ hε hexcess ha
    (E := (2 : ℝ)^s.primes.card * Real.exp (-a))
    (A := Real.exp b) (h := h) (mul_pos (pow_pos (by norm_num) _) (Real.exp_pos _))
    (Real.exp_pos _) (by
      rw [Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 2) _).ne' (Real.exp_pos _).ne',
        Real.log_pow, Real.log_exp]
      linarith) (by
      rw [← Real.exp_add]
      have he : b + -ε^2 / (2 * ∑ p : s.primes,
          (((‖Real.log (p : ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ)) ≤ -a := by
        rw [neg_div]
        linarith
      exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he)
        (pow_nonneg (by norm_num) _)).trans_eq (mul_comm _ _)) hbexp
  simpa only [Real.exp_neg] using hh

def orientedRectangle (e : ℂ) (R W : ℝ) : Set GaussianInt :=
  {z | |(star e * (z : ℂ)).re| ≤ R ∧ |(star e * (z : ℂ)).im| ≤ W}

theorem rectangle_norm_bound {e : ℂ} (he : ‖e‖ = 1) {R W : ℝ}
    (hW : 0 ≤ W) (hWR : W ≤ R) {z : GaussianInt} (hz : z ∈ orientedRectangle e R W) :
    (z.norm : ℝ) ≤ 2 * R^2 := by
  have hnorm : ‖star e * (z : ℂ)‖ = ‖(z : ℂ)‖ := by
    rw [norm_mul, norm_star, he, one_mul]
  rw [norm_square_complex, ← hnorm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hx : (star e * (z : ℂ)).re ^ 2 ≤ R^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg ((star e * (z : ℂ)).re))
      (hW.trans hWR)).mpr hz.1
  have hy : (star e * (z : ℂ)).im ^ 2 ≤ W^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg ((star e * (z : ℂ)).im)) hW).mpr hz.2
  have hww := (sq_le_sq₀ hW (hW.trans hWR)).mpr hWR
  linarith

theorem determinant_rotated (e : ℂ) (he : ‖e‖ = 1) (z w : GaussianInt) :
    (determinant z w : ℝ) =
      (star e * (z : ℂ)).re * (star e * (w : ℂ)).im -
      (star e * (z : ℂ)).im * (star e * (w : ℂ)).re := by
  have hsq : e.re^2 + e.im^2 = 1 := by
    have hh := Complex.normSq_eq_norm_sq e
    rw [he] at hh
    simpa [Complex.normSq_apply, pow_two] using hh
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    ← GaussianInt.intCast_re, ← GaussianInt.intCast_im, determinant, Int.cast_sub, Int.cast_mul]
  linarith [congrArg (fun x : ℝ => x * ((z.re : ℝ) * w.im - z.im * w.re)) hsq]

theorem rectangle_determinant_bound {e : ℂ} (he : ‖e‖ = 1) {R W : ℝ}
    (hR : 0 ≤ R) (hW : 0 ≤ W) {z w : GaussianInt}
    (hz : z ∈ orientedRectangle e R W) (hw : w ∈ orientedRectangle e R W) :
    (|determinant z w| : ℝ) ≤ 2*R*W := by
  rw [determinant_rotated e he]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_mul]
  have h1 := mul_le_mul hz.1 hw.2 (abs_nonneg _) hR
  have h2 := mul_le_mul hz.2 hw.1 (abs_nonneg _) hW
  linarith

theorem rectangle_cube_growth {r : ℕ} {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/4)
    (hlarge : 1000 ≤ d^3 * r) :
    let h := ⌊d * r / 10⌋₊
    d^3 * r / 5120 ≤ (h : ℝ) * Real.log (1 + (d^2 * r / 64) / ((r : ℝ) * Real.log 2)) := by
  dsimp only
  have hr : 0 < (r : ℝ) := by
    by_contra h
    have hr0 : (r : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
    rw [hr0, mul_zero] at hlarge
    norm_num at hlarge
  have loglo : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have loghi : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlog : 0 < Real.log 2 := lt_of_lt_of_le (by norm_num) loglo
  have hdle : d ≤ 1 := by linarith
  have hsq : d^2 ≤ 1 := by linarith [mul_le_mul hdle hdle hd.le zero_le_one]
  have hdr : d^3 * r ≤ d * r := by
    exact mul_le_mul_of_nonneg_right (by linarith [mul_nonneg hd.le (sub_nonneg.mpr hsq)]) hr.le
  have hfloor : d * r / 20 ≤ (⌊d * r / 10⌋₊ : ℝ) := by
    have hh := Nat.lt_floor_add_one (d * r / 10)
    have hdrl : 1000 ≤ d * r := hlarge.trans hdr
    linarith
  have heq : (d^2 * r / 64) / ((r : ℝ) * Real.log 2) = d^2 / (64 * Real.log 2) := by
    field_simp
  let δ := d^2 / (64 * Real.log 2)
  have hδ : 0 ≤ δ := div_nonneg (sq_nonneg _) (by positivity)
  have hδ1 : δ ≤ 1 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hlog)).mpr
    linarith
  have hδlo : d^2 / 64 ≤ δ := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hlog)).mpr
    linarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr loghi)]
  have hlogδ : δ/2 ≤ Real.log (1+δ) := by
    apply le_trans ?_ (Real.le_log_one_add_of_nonneg hδ)
    apply (le_div_iff₀ (by linarith : 0 < δ+2)).mpr
    linarith [mul_nonneg hδ (sub_nonneg.mpr hδ1)]
  rw [heq]
  change _ ≤ (⌊d * r / 10⌋₊ : ℝ) * Real.log (1+δ)
  have hm := mul_le_mul hfloor hlogδ (by linarith) (Nat.cast_nonneg _)
  have hm' : d^3 * r / 2560 ≤ (d*r/20) * (δ/2) := by
    have := mul_le_mul_of_nonneg_left hδlo (by positivity : 0 ≤ d*r/40)
    linarith
  have hnon : 0 ≤ d^3 * r := by positivity
  linarith

theorem rectangle_linear_large {r d : ℝ} (hr : 0 ≤ r) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hlarge : 1000 ≤ d^3 * r) : 1000 ≤ d*r := by
  have hs : d^2 ≤ 1 := by nlinarith
  have hc : d^3 ≤ d := by linarith [mul_nonneg hd (sub_nonneg.mpr hs)]
  exact hlarge.trans (mul_le_mul_of_nonneg_right hc hr)

theorem rectangle_log_small {r : ℕ} {d t u l : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1/4) (ht : 1/2 ≤ t) (hu : 0 ≤ u) (hutu : u ≤ 2*t)
    (hl : (r : ℝ)*t ≤ l) (hlarge : 1000 ≤ d^3 * r) :
    Real.log 2 + (1-d)*l + (2*⌊d*r/10⌋₊ : ℕ)*u < l := by
  have hdr : 1000 ≤ d*r := rectangle_linear_large (Nat.cast_nonneg _) hd.le (by linarith) hlarge
  have hf : (⌊d*r/10⌋₊ : ℝ) ≤ d*r/10 := Nat.floor_le (by positivity)
  have hm : (2*⌊d*r/10⌋₊ : ℕ)*u ≤ (d*r/5)*(2*t) := by
    push_cast
    apply mul_le_mul (by linarith) hutu hu
    positivity
  have hdl := mul_le_mul_of_nonneg_left hl hd.le
  have hdt : 500 ≤ d*r*t := by
    have hh := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ d*r)
    linarith
  have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  linarith

theorem rectangle_log_excess {r : ℕ} {d t l : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/4)
    (ht : 1/2 ≤ t) (hl : (r : ℝ)*t ≤ l) (hlarge : 1000 ≤ d^3 * r) :
    d*l/2 ≤ l - ((1-d)*l + Real.log 2/2) := by
  have hdr : 1000 ≤ d*r := rectangle_linear_large (Nat.cast_nonneg _) hd.le (by linarith) hlarge
  have h1 := mul_le_mul_of_nonneg_left hl hd.le
  have h2 := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ d*r)
  have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  linarith

theorem rectangle_hoeffding_exponent {r d t l V : ℝ} (hr : 0 < r) (hd : 0 ≤ d)
    (ht : 0 < t) (hl : r*t ≤ l) (hV : 0 < V) (hVup : V ≤ r*t^2) :
    2*(d^2*r/64) ≤ (d*l/2)^2 / (2*V) := by
  have hdl : 0 ≤ d*r*t/2 := by positivity
  have hdl' : d*r*t/2 ≤ d*l/2 := by linarith [mul_le_mul_of_nonneg_left hl hd]
  have hs : (d*r*t/2)^2 ≤ (d*l/2)^2 := (sq_le_sq₀ hdl (hdl.trans hdl')).mpr hdl'
  have hden : 0 < 2*r*t^2 := by positivity
  calc
    2*(d^2*r/64) ≤ d^2*r/8 := by linarith [mul_nonneg (sq_nonneg d) hr.le]
    _ = (d*r*t/2)^2 / (2*r*t^2) := by field_simp; ring
    _ ≤ (d*l/2)^2 / (2*r*t^2) := div_le_div_of_nonneg_right hs hden.le
    _ ≤ (d*l/2)^2 / (2*V) := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)

theorem SplitSieve.log_period (s : SplitSieve) :
    Real.log (s.period : ℝ) = ∑ p : s.primes, Real.log (p : ℝ) := by
  classical
  unfold SplitSieve.period
  push_cast
  rw [Real.log_prod (fun p hp => by
    exact_mod_cast (s.prime_mem p hp).ne_zero)]
  exact (Finset.sum_coe_sort s.primes (fun p => Real.log (p : ℝ))).symm

noncomputable def SplitSieve.logVariance (s : SplitSieve) : ℝ :=
  ∑ p : s.primes, (((‖Real.log (p : ℝ)‖₊ / 2)^2 : ℝ≥0) : ℝ)

theorem SplitSieve.logVariance_pos (s : SplitSieve) (hr : 0 < s.primes.card) :
    0 < s.logVariance := by
  classical
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hr
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (s.prime_mem p hp).one_lt)
  apply Finset.sum_pos' (fun _ _ => by positivity)
  refine ⟨⟨p,hp⟩, Finset.mem_univ _, ?_⟩
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs,
    abs_of_pos hlog]
  positivity

theorem SplitSieve.logVariance_le (s : SplitSieve) {U : ℝ}
    (hU : 1 ≤ U) (hpU : ∀ p ∈ s.primes, (p : ℝ) ≤ U) :
    s.logVariance ≤ (s.primes.card : ℝ) * (Real.log U / 2)^2 := by
  classical
  calc
    _ ≤ ∑ _p : s.primes, (Real.log U / 2)^2 := by
      apply Finset.sum_le_sum
      intro p _
      have hp : 0 < (p : ℝ) := by exact_mod_cast (s.prime_mem p p.property).pos
      have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (s.prime_mem p p.property).one_le)
      have hle := Real.log_le_log hp (hpU p p.property)
      simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs,
        abs_of_nonneg hlog]
      exact (sq_le_sq₀ (by positivity) (div_nonneg (Real.log_nonneg hU) (by norm_num))).mpr (by linarith)
    _ = _ := by simp [nsmul_eq_mul]

theorem SplitSieve.signed_rectangle (s : SplitSieve)
    {T R W d : ℝ} {e : ℂ} (he : ‖e‖ = 1) (hT : 5 ≤ T)
    (hpT : ∀ p ∈ s.primes, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hd : 0 < d) (hd1 : d < 1/4)
    (harea : R*W ≤ (s.period : ℝ)^(1-d)) (hlarge : 1000 ≤ d^3*s.primes.card) :
    (signMeasure s.primes).real {σ | s.badSign (orientedRectangle e R W) σ} ≤
      Real.exp (-(d^3*s.primes.card/5120)) := by
  have hr : 0 < s.primes.card := by
    by_contra h
    have hz : s.primes.card = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.cast_zero, mul_zero] at hlarge
    norm_num at hlarge
  have hr' : 0 < (s.primes.card : ℝ) := by exact_mod_cast hr
  have hP : 0 < (s.period : ℝ) := by exact_mod_cast s.period_pos
  have hTpos : 0 < T := by linarith
  have hU : 1 ≤ 2*T := by linarith
  have hUpos : 0 < 2*T := by linarith
  have hWpos : 0 < W := by linarith
  have hRpos : 0 < R := lt_of_lt_of_le hWpos hWR
  have hRW : 0 < R*W := mul_pos hRpos hWpos
  have hlogT : 1/2 ≤ Real.log T := by
    have hlog2T := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ T)
    linarith [Real.log_two_gt_d9]
  have hlogU : Real.log (2*T) ≤ 2*Real.log T := by
    rw [Real.log_mul (by norm_num) hTpos.ne']
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ T)
    linarith
  have hlogP : (s.primes.card : ℝ)*Real.log T ≤ Real.log (s.period : ℝ) := by
    rw [s.log_period]
    calc
      _ = ∑ _p : s.primes, Real.log T := by simp [nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun p _ => Real.log_le_log hTpos (hpT p p.property).1)
  have hlogPpos : 0 < Real.log (s.period : ℝ) :=
    (mul_pos hr' (by linarith : 0 < Real.log T)).trans_le hlogP
  have hRarea : R ≤ R*W := by linarith [mul_le_mul_of_nonneg_left hW hRpos.le]
  have hlogR : Real.log R ≤ (1-d)*Real.log (s.period : ℝ) := by
    have hh := Real.log_le_log hRpos (hRarea.trans harea)
    simpa only [Real.log_rpow hP] using hh
  have hlogB : Real.log (2*R*W) ≤ Real.log 2 + (1-d)*Real.log (s.period : ℝ) := by
    have hh := Real.log_le_log hRW harea
    rw [Real.log_rpow hP] at hh
    have heq : 2*R*W = 2*(R*W) := by ring
    rw [heq, Real.log_mul (by norm_num) hRW.ne']
    linarith
  have hlogN : Real.log (2*R^2)/2 ≤ (1-d)*Real.log (s.period : ℝ) + Real.log 2/2 := by
    rw [Real.log_mul (by norm_num) (pow_pos hRpos 2).ne', Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  let h : ℕ := ⌊d*s.primes.card/10⌋₊
  have hsmall : (2*R*W) * (2*T)^(2*h) < (s.period : ℝ) := by
    apply (Real.log_lt_log_iff (mul_pos (by positivity) (pow_pos hUpos _)) hP).mp
    rw [Real.log_mul (by positivity : 2*R*W ≠ 0) (pow_pos hUpos _).ne', Real.log_pow]
    have hh := rectangle_log_small hd hd1.le hlogT (Real.log_nonneg hU) hlogU hlogP hlarge
    exact (add_le_add_left hlogB _).trans_lt hh
  have hV := s.logVariance_pos hr
  have hVup : s.logVariance ≤ (s.primes.card : ℝ)*(Real.log T)^2 := by
    apply (s.logVariance_le hU (fun p hp => (hpT p hp).2)).trans
    apply mul_le_mul_of_nonneg_left ?_ hr'.le
    apply (sq_le_sq₀ (div_nonneg (Real.log_nonneg hU) (by norm_num)) (by linarith : 0 ≤ Real.log T)).mpr
    linarith
  apply s.signed_region_exp_bound (orientedRectangle e R W) hr hU
    (fun p hp => (hpT p hp).2) (by positivity) (fun _ hw _ hw' =>
      rectangle_determinant_bound he hRpos.le hWpos.le hw hw') hsmall
    (fun _ hz => rectangle_norm_bound he hWpos.le hWR hz)
    (ε := d*Real.log (s.period : ℝ)/2) (a := d^2*s.primes.card/64) (h := h)
  · positivity
  · rw [← s.log_period]
    have hh := rectangle_log_excess hd hd1.le hlogT hlogP hlarge
    linarith
  · positivity
  · have hc : d^3 ≤ d^2 := by linarith [mul_nonneg (sq_nonneg d) (by linarith : 0 ≤ 1-d)]
    have hh := mul_le_mul_of_nonneg_right hc hr'.le
    linarith [mul_nonneg (sq_nonneg d) hr'.le]
  · exact rectangle_hoeffding_exponent hr' hd.le (by linarith) hlogP hV hVup
  · exact rectangle_cube_growth hd hd1.le hlarge

end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat
open MeasureTheory ProbabilityTheory
open scoped NNReal

open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def entropySum {α : Type uAlpha} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ a, Real.negMulLog (p a)

theorem gibbs_point {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (habs : q = 0 → p = 0) :
    p - q ≤ p * (Real.log p - Real.log q) := by
  by_cases hp0 : p = 0
  · simp [hp0, hq]
  have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm (fun h => hp0 (habs h)))
  have h := mul_le_mul_of_nonneg_left
    (Real.self_sub_one_le_mul_log (div_nonneg hp hq)) hq
  rw [Real.log_div hp0 hqp.ne'] at h
  have h1 : q*(p/q-1) = p-q := by field_simp
  have h2 : q*(p/q*(Real.log p-Real.log q)) = p*(Real.log p-Real.log q) := by field_simp
  rwa [h1,h2] at h

theorem gibbs_sum {α : Type uAlpha} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (habs : ∀ a, q a = 0 → p a = 0) (hsum : ∑ a, p a = ∑ a, q a) :
    0 ≤ ∑ a, p a * (Real.log (p a) - Real.log (q a)) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ => gibbs_point (hp a) (hq a) (habs a))
  simpa [Finset.sum_sub_distrib, hsum] using h

theorem entropySum_subadd {α : Type uAlpha} {β : Type uBeta} [Fintype α] [Fintype β]
    (p : α → β → ℝ) (hp : ∀ a b, 0 ≤ p a b) :
    (∑ a, ∑ b, Real.negMulLog (p a b)) + Real.negMulLog (∑ a, ∑ b, p a b) ≤
      (∑ a, Real.negMulLog (∑ b, p a b)) + ∑ b, Real.negMulLog (∑ a, p a b) := by
  classical
  let r := fun a => ∑ b, p a b
  let c := fun b => ∑ a, p a b
  let m := ∑ a, r a
  have hr : ∀ a, 0 ≤ r a := fun a => Finset.sum_nonneg (fun b _ => hp a b)
  have hc : ∀ b, 0 ≤ c b := fun b => Finset.sum_nonneg (fun a _ => hp a b)
  have hm : 0 ≤ m := Finset.sum_nonneg (fun a _ => hr a)
  have hpr : ∀ a b, p a b ≤ r a := fun a b =>
    Finset.single_le_sum (fun b' _ => hp a b') (Finset.mem_univ b)
  have hpc : ∀ a b, p a b ≤ c b := fun a b =>
    Finset.single_le_sum (fun a' _ => hp a' b) (Finset.mem_univ a)
  have hrm : ∀ a, r a ≤ m := fun a =>
    Finset.single_le_sum (fun a' _ => hr a') (Finset.mem_univ a)
  have hcm : ∑ b, c b = m := Finset.sum_comm
  by_cases hm0 : m = 0
  · have hz : ∀ a b, p a b = 0 := fun a b => le_antisymm (by simpa [hm0] using (hpr a b).trans (hrm a)) (hp a b)
    simp [hz]
  have hmp : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  let q := fun ab : α × β => r ab.1 * c ab.2 / m
  have hq : ∀ ab, 0 ≤ q ab := fun ab => div_nonneg (mul_nonneg (hr _) (hc _)) hm
  have habs : ∀ ab : α × β, q ab = 0 → p ab.1 ab.2 = 0 := by
    intro ab hh
    by_contra h
    have hpp : 0 < p ab.1 ab.2 := lt_of_le_of_ne (hp _ _) (Ne.symm h)
    have hrp : 0 < r ab.1 := hpp.trans_le (hpr _ _)
    have hcp : 0 < c ab.2 := hpp.trans_le (hpc _ _)
    exact (div_pos (mul_pos hrp hcp) hmp).ne' hh
  have hqsum : ∑ ab, q ab = m := by
    rw [Fintype.sum_prod_type]
    change (∑ a, ∑ b, r a*c b/m) = m
    have hi : ∀ a, (∑ b, r a*c b/m) = r a := by
      intro a
      calc
        _ = (r a*(∑ b, c b))/m := by rw [Finset.mul_sum, Finset.sum_div]
        _ = r a := by rw [hcm, mul_div_cancel_right₀ _ hm0]
    simp_rw [hi]
    rfl
  have hg := gibbs_sum (fun ab : α × β => p ab.1 ab.2) q (fun _ => hp _ _) hq habs
    (by rw [hqsum, Fintype.sum_prod_type])
  have ht : ∀ a b, p a b * (Real.log (p a b) - Real.log (q (a,b))) =
      p a b*Real.log (p a b) - p a b*Real.log (r a) - p a b*Real.log (c b) + p a b*Real.log m := by
    intro a b
    by_cases hz : p a b = 0
    · simp [hz]
    have hpp : 0 < p a b := lt_of_le_of_ne (hp _ _) (Ne.symm hz)
    have hrp : 0 < r a := hpp.trans_le (hpr _ _)
    have hcp : 0 < c b := hpp.trans_le (hpc _ _)
    dsimp [q]
    rw [Real.log_div (mul_pos hrp hcp).ne' hm0, Real.log_mul hrp.ne' hcp.ne']
    ring
  have hrow : (∑ a, ∑ b, p a b * Real.log (r a)) = ∑ a, r a*Real.log (r a) := by
    simp_rw [← Finset.sum_mul]
    rfl
  have hcol : (∑ a, ∑ b, p a b * Real.log (c b)) = ∑ b, c b*Real.log (c b) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    rfl
  have htot : (∑ a, ∑ b, p a b * Real.log m) = m*Real.log m := by
    simp_rw [← Finset.sum_mul]
    rfl
  rw [Fintype.sum_prod_type] at hg
  simp_rw [ht, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hg
  rw [hrow,hcol,htot] at hg
  change (∑ a, ∑ b, Real.negMulLog (p a b)) + Real.negMulLog m ≤
    (∑ a, Real.negMulLog (r a)) + ∑ b, Real.negMulLog (c b)
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  linarith

theorem negMulLog_sum_le {α : Type uAlpha} [Fintype α] (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) :
    Real.negMulLog (∑ a, p a) ≤ ∑ a, Real.negMulLog (p a) := by
  have ht : ∀ a, -p a * Real.log (∑ b, p b) ≤ Real.negMulLog (p a) := by
    intro a
    by_cases hz : p a = 0
    · simp [hz]
    have hpos := lt_of_le_of_ne (hp a) (Ne.symm hz)
    have hle : p a ≤ ∑ b, p b := Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a)
    have hh := mul_le_mul_of_nonneg_left (Real.log_le_log hpos hle) (hp a)
    unfold Real.negMulLog
    linarith
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun a _ => ht a)
  simpa only [← Finset.sum_mul, Finset.sum_neg_distrib, Real.negMulLog] using hh

structure FinLaw (α : Type uAlpha) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  sum_one : ∑ a, mass a = 1

namespace FinLaw
variable {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} {Ω : Type uOmega} [Fintype α] [Fintype β] [Fintype γ] [Fintype Ω]

instance : CoeFun (FinLaw α) (fun _ => α → ℝ) := ⟨mass⟩

@[ext] theorem ext {p q : FinLaw α} (h : ∀ a, p a = q a) : p = q := by
  cases p; cases q; congr; exact funext h

theorem le_one (p : FinLaw α) (a : α) : p a ≤ 1 := by
  rw [← p.sum_one]
  exact Finset.single_le_sum (fun x _ => p.nonneg x) (Finset.mem_univ a)

theorem nonempty (p : FinLaw α) : Nonempty α := by
  by_contra h
  have : IsEmpty α := not_nonempty_iff.mp h
  simpa using p.sum_one

noncomputable def entropy (p : FinLaw α) : ℝ := entropySum p

theorem entropy_nonneg (p : FinLaw α) : 0 ≤ p.entropy :=
  Finset.sum_nonneg (fun a _ => Real.negMulLog_nonneg (p.nonneg a) (p.le_one a))

theorem entropy_le_log_card (p : FinLaw α) : p.entropy ≤ Real.log (Fintype.card α) := by
  have := p.nonempty
  have hn : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := gibbs_sum (fun a => p a) (fun _ => (Fintype.card α : ℝ)⁻¹) p.nonneg
    (fun _ => by positivity) (fun _ h => False.elim ((inv_pos.mpr hn).ne' h)) (by simp [p.sum_one, hn.ne'])
  have heq : (∑ a, p a * (Real.log (p a) - Real.log (Fintype.card α : ℝ)⁻¹)) =
      -p.entropy + Real.log (Fintype.card α) := by
    simp only [Real.log_inv, sub_neg_eq_add, mul_add, Finset.sum_add_distrib,
      ← Finset.sum_mul, p.sum_one, one_mul, entropy, entropySum, Real.negMulLog]
    rw [← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [heq] at h
  linarith

noncomputable def map (p : FinLaw α) (f : α → β) : FinLaw β := by
  classical
  exact {
    mass := fun b => ∑ a, if f a = b then p a else 0
    nonneg := fun b => Finset.sum_nonneg (fun a _ => by split_ifs; exact p.nonneg a; exact le_rfl)
    sum_one := by rw [Finset.sum_comm]; simpa using p.sum_one }

@[simp] theorem map_mass (p : FinLaw α) (f : α → β) (b : β) :
    p.map f b = ∑ a, if f a = b then p a else 0 := by
  classical
  rfl

@[simp] theorem map_id (p : FinLaw α) : p.map id = p := by
  classical
  ext a
  simp

@[simp] theorem map_comp (p : FinLaw α) (f : α → β) (g : β → γ) :
    (p.map f).map g = p.map (g ∘ f) := by
  classical
  ext c
  simp only [map_mass]
  have he (b : β) : (if g b = c then ∑ a, if f a = b then p a else 0 else 0) =
      ∑ a, if f a = b ∧ g b = c then p a else 0 := by
    by_cases h : g b = c <;> simp [h]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_and]

noncomputable def H (p : FinLaw Ω) (X : Ω → α) : ℝ := (p.map X).entropy

noncomputable def condH (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) : ℝ :=
  p.H (fun ω => (X ω,Y ω)) - p.H Y

theorem H_eq_sum (p : FinLaw Ω) (X : Ω → α) :
    p.H X = -∑ ω, p ω * Real.log (p.map X (X ω)) := by
  classical
  unfold H entropy entropySum
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  congr 1
  calc
    _ = ∑ a, ∑ ω, (if X ω = a then p ω else 0) * Real.log (p.map X a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [map_mass, Finset.sum_mul]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω _
      simp [ite_mul]

theorem H_eq_of_fibers (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β)
    (hf : ∀ ω ω', X ω = X ω' ↔ Y ω = Y ω') : p.H X = p.H Y := by
  rw [H_eq_sum,H_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  have hh : p.map X (X ω) = p.map Y (Y ω) := by
    simp only [map_mass]
    apply Finset.sum_congr rfl
    intro ω' _
    rw [hf]
  rw [hh]

theorem H_comp_injective (p : FinLaw Ω) (X : Ω → α) (f : α → β)
    (hf : Function.Injective f) : p.H (f ∘ X) = p.H X :=
  p.H_eq_of_fibers _ _ (fun _ _ => hf.eq_iff)

theorem H_pair_comm (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.H (fun ω => (X ω,Y ω)) = p.H (fun ω => (Y ω,X ω)) := by
  apply p.H_eq_of_fibers
  simp only [Prod.mk.injEq, and_comm, implies_true]

theorem H_pair_assoc (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.H (fun ω => (X ω,(Y ω,Z ω))) = p.H (fun ω => ((X ω,Y ω),Z ω)) := by
  apply p.H_eq_of_fibers
  simp only [Prod.mk.injEq, and_assoc, implies_true]

theorem H_pair_function (p : FinLaw Ω) (X : Ω → α) (f : α → β) :
    p.H (fun ω => (X ω,f (X ω))) = p.H X := by
  apply p.H_eq_of_fibers
  intro ω ω'
  simp only [Prod.mk.injEq]
  exact ⟨And.left,fun h => ⟨h,congrArg f h⟩⟩

@[simp] theorem H_map (p : FinLaw Ω) (X : Ω → α) (f : α → β) :
    (p.map X).H f = p.H (f ∘ X) := by simp [H]

@[simp] theorem map_fst_mass (p : FinLaw (α × β)) (a : α) :
    p.map Prod.fst a = ∑ b, p (a,b) := by
  rw [map_mass,Fintype.sum_prod_type,Finset.sum_comm]
  simp

@[simp] theorem map_snd_mass (p : FinLaw (α × β)) (b : β) :
    p.map Prod.snd b = ∑ a, p (a,b) := by
  simp [map_mass,Fintype.sum_prod_type]

theorem entropy_ge_snd (p : FinLaw (α × β)) : (p.map Prod.snd).entropy ≤ p.entropy := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun b _ => negMulLog_sum_le (fun a => p (a,b)) (fun _ => p.nonneg _))
  rw [Finset.sum_comm] at h
  simpa only [entropy,entropySum,map_snd_mass,Fintype.sum_prod_type] using h

theorem entropy_subadd (p : FinLaw (α × β)) :
    p.entropy ≤ (p.map Prod.fst).entropy + (p.map Prod.snd).entropy := by
  have h := entropySum_subadd (fun a b => p (a,b)) (fun _ _ => p.nonneg _)
  have hs : (∑ a, ∑ b, p (a,b)) = 1 := by simpa only [Fintype.sum_prod_type] using p.sum_one
  rw [hs,Real.negMulLog_one,add_zero] at h
  simpa only [entropy,entropySum,map_fst_mass,map_snd_mass,Fintype.sum_prod_type] using h

theorem H_pair_ge_snd (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.H Y ≤ p.H (fun ω => (X ω,Y ω)) := by
  have h := (p.map (fun ω => (X ω,Y ω))).entropy_ge_snd
  simpa only [map_comp,Function.comp_def,H] using h

theorem H_pair_subadd (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.H (fun ω => (X ω,Y ω)) ≤ p.H X + p.H Y := by
  have h := (p.map (fun ω => (X ω,Y ω))).entropy_subadd
  simpa only [map_comp,Function.comp_def,H] using h

theorem condH_nonneg (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) : 0 ≤ p.condH X Y :=
  sub_nonneg.mpr (p.H_pair_ge_snd X Y)

theorem condH_le_H (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) : p.condH X Y ≤ p.H X := by
  have h := p.H_pair_subadd X Y
  unfold condH
  linarith

theorem H_le_condH_add (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.H X ≤ p.condH X Y + p.H Y := by
  have h := p.H_pair_ge_snd Y X
  rw [p.H_pair_comm Y X] at h
  simpa only [condH,sub_add_cancel] using h

theorem entropy_strong_subadd (p : FinLaw (α × (β × γ))) :
    p.entropy + (p.map (fun x => x.2.1)).entropy ≤
      (p.map (fun x => (x.1,x.2.1))).entropy + (p.map Prod.snd).entropy := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun b _ =>
    entropySum_subadd (fun a c => p (a,(b,c))) (fun _ _ => p.nonneg _))
  have hmid (b : β) : p.map (fun x => x.2.1) b = ∑ a, ∑ c, p (a,(b,c)) := by
    simp only [map_mass,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    simp
  have hleft (a : α) (b : β) : p.map (fun x => (x.1,x.2.1)) (a,b) = ∑ c, p (a,(b,c)) := by
    simp [map_mass,Fintype.sum_prod_type,Prod.mk.injEq,ite_and]
    rw [Finset.sum_comm]
    simp
  have hfull : (∑ b, ∑ a, ∑ c, Real.negMulLog (p (a,(b,c)))) = p.entropy := by
    rw [Finset.sum_comm]
    simp only [entropy,entropySum,Fintype.sum_prod_type]
  have hxy : (∑ b, ∑ a, Real.negMulLog (∑ c, p (a,(b,c)))) =
      (p.map (fun x => (x.1,x.2.1))).entropy := by
    rw [Finset.sum_comm]
    simp only [entropy,entropySum,Fintype.sum_prod_type,hleft]
  simp only [Finset.sum_add_distrib] at h
  rw [hfull,hxy] at h
  simpa only [entropy,entropySum,Fintype.sum_prod_type,hmid,map_snd_mass] using h

theorem H_strong_subadd (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.H (fun ω => (X ω,(Y ω,Z ω))) + p.H Y ≤
      p.H (fun ω => (X ω,Y ω)) + p.H (fun ω => (Y ω,Z ω)) := by
  have h := (p.map (fun ω => (X ω,(Y ω,Z ω)))).entropy_strong_subadd
  simpa only [map_comp,Function.comp_def,H] using h

theorem condH_mono (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.condH X (fun ω => (Y ω,Z ω)) ≤ p.condH X Y := by
  have h := p.H_strong_subadd X Y Z
  unfold condH
  linarith

noncomputable def mutualInfo (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) : ℝ :=
  p.H X - p.condH X Y

noncomputable def condMutualInfo {δ : Type uDelta} [Fintype δ] (p : FinLaw Ω)
    (X : Ω → α) (Y : Ω → β) (Z : Ω → δ) : ℝ :=
  p.condH X Z - p.condH X (fun ω => (Y ω,Z ω))

theorem mutualInfo_nonneg (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    0 ≤ p.mutualInfo X Y := sub_nonneg.mpr (p.condH_le_H X Y)

theorem condH_pair_comm (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.condH X (fun ω => (Y ω,Z ω)) = p.condH X (fun ω => (Z ω,Y ω)) := by
  unfold condH
  congr 1
  · apply p.H_eq_of_fibers
    simp only [Prod.mk.injEq,and_comm,implies_true]
  · exact p.H_pair_comm Y Z

theorem condMutualInfo_nonneg (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    0 ≤ p.condMutualInfo X Y Z := by
  unfold condMutualInfo
  rw [condH_pair_comm]
  exact sub_nonneg.mpr (p.condH_mono X Z Y)

theorem entropySum_scale (p : α → ℝ) (c : ℝ) :
    entropySum (fun a => c*p a) = c*entropySum p + (∑ a, p a)*Real.negMulLog c := by
  simp only [entropySum, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem entropySum_le_mass_log_card (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) :
    entropySum p ≤ (∑ a, p a)*Real.log (Fintype.card α) + Real.negMulLog (∑ a, p a) := by
  let m := ∑ a, p a
  have hm : 0 ≤ m := Finset.sum_nonneg (fun a _ => hp a)
  by_cases hm0 : m = 0
  · have hz : ∀ a, p a = 0 := by
      intro a
      have hle : p a ≤ m := Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a)
      exact le_antisymm (by simpa [hm0] using hle) (hp a)
    simp [entropySum,hz]
  let q : FinLaw α := {
    mass := fun a => p a/m
    nonneg := fun a => div_nonneg (hp a) hm
    sum_one := by rw [← Finset.sum_div]; exact div_self hm0 }
  have h := mul_le_mul_of_nonneg_left q.entropy_le_log_card hm
  have he : entropySum p = m*q.entropy + Real.negMulLog m := by
    have hs : (fun a => m*q a) = p := by ext a; dsimp [q]; field_simp
    rw [← hs, entropySum_scale, q.sum_one, one_mul]
    rfl
  rw [he]
  exact add_le_add_left h _

theorem entropySum_le_mass_log_support (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (S : Finset α) (hs : ∀ a, a ∉ S → p a = 0) :
    entropySum p ≤ (∑ a, p a)*Real.log S.card + Real.negMulLog (∑ a, p a) := by
  classical
  have he : entropySum p = entropySum (fun a : S => p a) := by
    unfold entropySum
    rw [← Finset.sum_subtype S (fun _ => Iff.rfl) (fun a => Real.negMulLog (p a))]
    exact (Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => by rw [hs a ha,Real.negMulLog_zero])).symm
  have hm : (∑ a, p a) = ∑ a : S, p a := by
    rw [← Finset.sum_subtype S (fun _ => Iff.rfl) p]
    exact (Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => hs a ha)).symm
  rw [he,hm]
  simpa using entropySum_le_mass_log_card (fun a : S => p a) (fun a => hp a)

theorem condH_le_support (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β)
    (L : β → Finset α) (hs : ∀ ω, p ω ≠ 0 → X ω ∈ L (Y ω)) :
    p.condH X Y ≤ ∑ b, p.map Y b * Real.log (L b).card := by
  classical
  let q := p.map (fun ω => (X ω,Y ω))
  have hzero : ∀ b a, a ∉ L b → q (a,b) = 0 := by
    intro b a ha
    change p.map (fun ω => (X ω,Y ω)) (a,b) = 0
    rw [map_mass]
    apply Finset.sum_eq_zero
    intro ω _
    split_ifs with he
    · have he' := Prod.mk.inj he
      by_contra hn
      have hmem := hs ω hn
      rw [he'.1,he'.2] at hmem
      exact ha hmem
    · rfl
  have h := Finset.sum_le_sum (s := Finset.univ) (fun b _ =>
    entropySum_le_mass_log_support (fun a => q (a,b)) (fun a => q.nonneg _) (L b) (hzero b))
  have hm (b : β) : (∑ a, q (a,b)) = p.map Y b := by
    rw [← map_snd_mass,map_comp]
    rfl
  simp_rw [hm] at h
  rw [Finset.sum_add_distrib] at h
  have hfull : (∑ b, entropySum (fun a => q (a,b))) = p.H (fun ω => (X ω,Y ω)) := by
    unfold entropySum
    rw [Finset.sum_comm]
    simp only [H,entropy,entropySum,Fintype.sum_prod_type,q]
  rw [hfull] at h
  change p.condH X Y ≤ _
  unfold condH
  have hh : (∑ b, Real.negMulLog (p.map Y b)) = p.H Y := rfl
  rw [hh] at h
  linarith

noncomputable def mix (p : FinLaw Ω) (q : Ω → FinLaw α) : FinLaw α := {
  mass := fun a => ∑ ω, p ω * q ω a
  nonneg := fun a => Finset.sum_nonneg (fun ω _ => mul_nonneg (p.nonneg ω) ((q ω).nonneg a))
  sum_one := by rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum, sum_one, mul_one]; exact p.sum_one }

@[simp] theorem mix_mass (p : FinLaw Ω) (q : Ω → FinLaw α) (a : α) :
    p.mix q a = ∑ ω, p ω * q ω a := rfl

theorem entropy_mix_ge (p : FinLaw Ω) (q : Ω → FinLaw α) :
    (∑ ω, p ω * (q ω).entropy) ≤ (p.mix q).entropy := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
    Real.concaveOn_negMulLog.le_map_sum (fun ω _ => p.nonneg ω) p.sum_one
      (fun ω _ => (q ω).nonneg a))
  change (∑ ω, p ω * ∑ a, Real.negMulLog (q ω a)) ≤ _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simpa only [entropy,entropySum,mix_mass,smul_eq_mul] using h

@[simp] theorem H_const (p : FinLaw Ω) (a : α) : p.H (fun _ => a) = 0 := by
  rw [H_eq_sum]
  simp [p.sum_one]

theorem H_bool (p : FinLaw Ω) (E : Ω → Bool) :
    p.H E = Real.binEntropy (p.map E true) := by
  have hs := (p.map E).sum_one
  simp only [Fintype.sum_bool] at hs
  have hf : p.map E false = 1 - p.map E true := by linarith
  simp only [H,entropy,entropySum,Fintype.sum_bool,hf,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

theorem condH_le_reveal (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.condH X Y ≤ p.H Z + p.condH X (fun ω => (Y ω,Z ω)) := by
  have h1 := p.H_pair_ge_snd Z (fun ω => (X ω,Y ω))
  have he : p.H (fun ω => (Z ω,(X ω,Y ω))) = p.H (fun ω => (X ω,(Y ω,Z ω))) := by
    apply p.H_eq_of_fibers
    simp only [Prod.mk.injEq]
    tauto
  rw [he] at h1
  have h2 := p.H_pair_subadd Y Z
  unfold condH
  linarith

omit [Fintype α] in

theorem log_card_le_real (S : Finset α) {b : ℝ} (hb : 1 ≤ b) (hs : (S.card : ℝ) ≤ b) :
    Real.log S.card ≤ Real.log b := by
  by_cases hz : S.card = 0
  · simpa [hz] using Real.log_nonneg hb
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) hs

theorem short_list (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β)
    (L : β → Finset α) (E : Ω → Bool) {b : ℝ} (hb : 1 ≤ b)
    (hs : ∀ ω, p ω ≠ 0 → E ω = true → X ω ∈ L (Y ω) ∧ ((L (Y ω)).card : ℝ) ≤ b) :
    p.condH X Y ≤ Real.binEntropy (p.map E true) +
      p.map E true * Real.log b + (1-p.map E true)*Real.log (Fintype.card α) := by
  classical
  let L' : β × Bool → Finset α := fun ye =>
    if ye.2 = true then if ((L ye.1).card : ℝ) ≤ b then L ye.1 else ∅ else Finset.univ
  have hs' : ∀ ω, p ω ≠ 0 → X ω ∈ L' (Y ω,E ω) := by
    intro ω hn
    by_cases he : E ω = true
    · have hh := hs ω hn he
      simpa [L',he,hh.2] using hh.1
    · simp [L',he]
  have hc := p.condH_le_support X (fun ω => (Y ω,E ω)) L' hs'
  have hcard (y : β) (e : Bool) :
      Real.log (L' (y,e)).card ≤ if e = true then Real.log b else Real.log (Fintype.card α) := by
    cases e
    · simp [L']
    · simp only [L',ite_true]
      split_ifs with hh
      · exact log_card_le_real _ hb hh
      · simpa using Real.log_nonneg hb
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun ye _ =>
    mul_le_mul_of_nonneg_left (hcard ye.1 ye.2) ((p.map (fun ω => (Y ω,E ω))).nonneg ye))
  have hm (e : Bool) : (∑ y, p.map (fun ω => (Y ω,E ω)) (y,e)) = p.map E e := by
    rw [← map_snd_mass,map_comp]
    rfl
  have hsum : (∑ ye : β × Bool, p.map (fun ω => (Y ω,E ω)) ye *
      (if ye.2 = true then Real.log b else Real.log (Fintype.card α))) =
      p.map E true*Real.log b + (1-p.map E true)*Real.log (Fintype.card α) := by
    rw [Fintype.sum_prod_type,Finset.sum_comm,Fintype.sum_bool]
    simp only [Bool.false_eq_true,ite_false,ite_true,← Finset.sum_mul,hm]
    have htotal := (p.map E).sum_one
    simp only [Fintype.sum_bool] at htotal
    congr 2
    linarith
  rw [hsum] at hh
  have h := p.condH_le_reveal X Y E
  rw [H_bool] at h
  linarith

theorem short_list_deficit (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β)
    (L : β → Finset α) (E : Ω → Bool) {b : ℝ} (hb : 1 ≤ b)
    (hs : ∀ ω, p ω ≠ 0 → E ω = true → X ω ∈ L (Y ω) ∧ ((L (Y ω)).card : ℝ) ≤ b) :
    p.map E true * (Real.log (Fintype.card α) - Real.log b) - Real.binEntropy (p.map E true)
      ≤ Real.log (Fintype.card α) - p.condH X Y := by
  have h := p.short_list X Y L E hb hs
  linarith

theorem low_mass_deficit (p : FinLaw α) (S : Finset α)
    (hs : ∀ a ∈ S, p a ≤ 3 / (8 * (Fintype.card α : ℝ))) :
    (S.card : ℝ) / (8 * (Fintype.card α : ℝ)) ≤ Real.log (Fintype.card α) - p.entropy := by
  classical
  have := p.nonempty
  have hn : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  let u : ℝ := (Fintype.card α : ℝ)⁻¹
  have hu : 0 < u := inv_pos.mpr hn
  let d := fun a => p a * (Real.log (p a) - Real.log u) - p a + u
  have hd : ∀ a, 0 ≤ d a := by
    intro a
    have h := gibbs_point (p.nonneg a) hu.le (fun hz => False.elim (hu.ne' hz))
    dsimp [d]
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); norm_num at h ⊢; exact h
  have hlow : ∀ a ∈ S, u/8 ≤ d a := by
    intro a ha
    have h := gibbs_point (p.nonneg a) (show 0 ≤ u/2 by positivity)
      (fun hz => False.elim ((div_pos hu (by norm_num : (0:ℝ)<2)).ne' hz))
    rw [Real.log_div hu.ne' (by norm_num : (2:ℝ) ≠ 0)] at h
    have hlog := mul_le_mul_of_nonneg_left hlog2 (p.nonneg a)
    have hpa : p a ≤ 3*u/8 := by simpa only [u,div_eq_mul_inv,mul_inv_rev,mul_assoc] using hs a ha
    dsimp [d]
    linarith
  have hsum : (∑ a, d a) = Real.log (Fintype.card α) - p.entropy := by
    simp only [d, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul,p.sum_one,one_mul,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,u,Real.log_inv]
    rw [mul_inv_cancel₀ hn.ne']
    simp only [entropy,entropySum,Real.negMulLog,neg_mul,Finset.sum_neg_distrib]
    ring
  have hh := Finset.sum_le_sum (s := S) hlow
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun a _ _ => hd a)
  have hfinal := hh.trans hsub
  rw [hsum] at hfinal
  simpa only [Finset.sum_const,nsmul_eq_mul,u,div_eq_mul_inv,mul_inv_rev,mul_assoc] using hfinal

end FinLaw

end GaussianMoat

end OAI
end
end

section
section
namespace OAI

namespace GaussianMoat

section
open scoped BigOperators

def colorEdge (a b : Fin 3) : ℤ :=
  if a = 0 ∧ b = 1 then 1 else if a = 1 ∧ b = 0 then -1 else 0

def Tricolored (a b c : Fin 3) : Prop := a ≠ b ∧ b ≠ c ∧ a ≠ c

theorem colorEdge_add {a b c : Fin 3} (h : ¬ Tricolored a b c) :
    colorEdge a b + colorEdge b c = colorEdge a c := by
  unfold Tricolored at h
  revert a b c
  decide

theorem colorEdge_zero_left (a b : Fin 3) (ha : a ≠ 0) (hb : b ≠ 0) :
    colorEdge a b = 0 := by simp [colorEdge,ha,hb]

theorem colorEdge_zero_one (a b : Fin 3) (ha : a ≠ 1) (hb : b ≠ 1) :
    colorEdge a b = 0 := by simp [colorEdge,ha,hb]

theorem colorEdge_binary (a b : Fin 3) (ha : a ≠ 2) (hb : b ≠ 2) :
    colorEdge a b = (b.val : ℤ) - a.val := by
  revert a b
  decide

theorem discrete_rectangle_sperner (c : ℕ → ℕ → Fin 3) (m n : ℕ)
    (hbottom : ∀ i ≤ m, c i 0 = 0)
    (htop : ∀ i ≤ m, c i n ≠ 0)
    (hleft : ∀ j ≤ n, c 0 j ≠ 2)
    (hright : ∀ j ≤ n, c m j ≠ 1) :
    ∃ i < m, ∃ j < n,
      Tricolored (c i j) (c (i+1) j) (c (i+1) (j+1)) ∨
      Tricolored (c i j) (c i (j+1)) (c (i+1) (j+1)) := by
  by_contra h
  have hcell (i j : ℕ) (hi : i < m) (hj : j < n) :
      colorEdge (c i j) (c (i+1) j) - colorEdge (c i (j+1)) (c (i+1) (j+1)) =
      colorEdge (c i j) (c i (j+1)) - colorEdge (c (i+1) j) (c (i+1) (j+1)) := by
    have h1 : ¬ Tricolored (c i j) (c (i+1) j) (c (i+1) (j+1)) :=
      fun hh => h ⟨i,hi,j,hj,Or.inl hh⟩
    have h2 : ¬ Tricolored (c i j) (c i (j+1)) (c (i+1) (j+1)) :=
      fun hh => h ⟨i,hi,j,hj,Or.inr hh⟩
    have he1 := colorEdge_add h1
    have he2 := colorEdge_add h2
    omega
  have hsum := Finset.sum_congr (s₁ := Finset.range n) rfl (fun j hj =>
    Finset.sum_congr (s₁ := Finset.range m) rfl (fun i hi =>
      hcell i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)))
  have hl : (∑ j ∈ Finset.range n, ∑ i ∈ Finset.range m,
      (colorEdge (c i j) (c (i+1) j) - colorEdge (c i (j+1)) (c (i+1) (j+1)))) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.sum_range_sub']
    rw [hbottom i (Nat.le_of_lt (Finset.mem_range.mp hi)),
      hbottom (i+1) (Finset.mem_range.mp hi)]
    rw [colorEdge_zero_left _ _ (htop i (Nat.le_of_lt (Finset.mem_range.mp hi)))
      (htop (i+1) (Finset.mem_range.mp hi))]
    rfl
  have hr : (∑ j ∈ Finset.range n, ∑ i ∈ Finset.range m,
      (colorEdge (c i j) (c i (j+1)) - colorEdge (c (i+1) j) (c (i+1) (j+1)))) = 1 := by
    have he (j : ℕ) (hj : j ∈ Finset.range n) :
        (∑ i ∈ Finset.range m, (colorEdge (c i j) (c i (j+1)) -
          colorEdge (c (i+1) j) (c (i+1) (j+1)))) = ((c 0 (j+1)).val : ℤ) - (c 0 j).val := by
      rw [Finset.sum_range_sub']
      rw [colorEdge_zero_one _ _ (hright j (Nat.le_of_lt (Finset.mem_range.mp hj)))
        (hright (j+1) (Finset.mem_range.mp hj)),sub_zero,
        colorEdge_binary _ _ (hleft j (Nat.le_of_lt (Finset.mem_range.mp hj)))
          (hleft (j+1) (Finset.mem_range.mp hj))]
    rw [Finset.sum_congr rfl he,Finset.sum_range_sub (fun j => ((c 0 j).val : ℤ))]
    have hend : c 0 n = 1 := by
      have h0 := htop 0 (Nat.zero_le m)
      have h2 := hleft n le_rfl
      have hone : ∀ x : Fin 3, x ≠ 0 → x ≠ 2 → x = 1 := by decide
      exact hone _ h0 h2
    rw [hend,hbottom 0 (Nat.zero_le m)]
    norm_num
  rw [hl,hr] at hsum
  omega

noncomputable def pointColor (z : ℂ) : Fin 3 := if z.im < 0 then 0 else if z.re < 0 then 1 else 2

theorem pointColor_zero {z : ℂ} (h : pointColor z = 0) : z.im < 0 := by
  unfold pointColor at h
  split_ifs at h with hi hr
  · exact hi
  · exact False.elim ((by decide : (1 : Fin 3) ≠ 0) h)
  · exact False.elim ((by decide : (2 : Fin 3) ≠ 0) h)

theorem pointColor_one {z : ℂ} (h : pointColor z = 1) : z.re < 0 ∧ 0 ≤ z.im := by
  unfold pointColor at h
  split_ifs at h with hi hr
  · exact False.elim ((by decide : (0 : Fin 3) ≠ 1) h)
  · exact ⟨hr,le_of_not_gt hi⟩
  · exact False.elim ((by decide : (2 : Fin 3) ≠ 1) h)

theorem pointColor_two {z : ℂ} (h : pointColor z = 2) : 0 ≤ z.re ∧ 0 ≤ z.im := by
  unfold pointColor at h
  split_ifs at h with hi hr
  · exact False.elim ((by decide : (0 : Fin 3) ≠ 2) h)
  · exact False.elim ((by decide : (1 : Fin 3) ≠ 2) h)
  · exact ⟨le_of_not_gt hr,le_of_not_gt hi⟩

theorem tricolored_covers {a b c : Fin 3} (h : Tricolored a b c) (q : Fin 3) :
    q = a ∨ q = b ∨ q = c := by
  unfold Tricolored at h
  revert a b c q
  decide

theorem tricolored_norm_bound {x y z : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hxy : dist x y ≤ r) (hxz : dist x z ≤ r)
    (hc : Tricolored (pointColor x) (pointColor y) (pointColor z)) : ‖x‖ ≤ 2*r := by
  have he (q : Fin 3) : ∃ w : ℂ, pointColor w = q ∧ dist x w ≤ r := by
    rcases tricolored_covers hc q with h | h | h
    · exact ⟨x,h.symm,by simpa using hr⟩
    · exact ⟨y,h.symm,hxy⟩
    · exact ⟨z,h.symm,hxz⟩
  obtain ⟨w0,h0,hd0⟩ := he 0
  obtain ⟨w1,h1,hd1⟩ := he 1
  obtain ⟨w2,h2,hd2⟩ := he 2
  have hc0 := pointColor_zero h0
  have hc1 := pointColor_one h1
  have hc2 := pointColor_two h2
  have hRe (w : ℂ) (hd : dist x w ≤ r) : -r ≤ x.re-w.re ∧ x.re-w.re ≤ r := by
    apply abs_le.mp
    have hh : |x.re-w.re| ≤ dist x w := by simpa only [Complex.sub_re,dist_eq_norm] using Complex.abs_re_le_norm (x-w)
    exact hh.trans hd
  have hIm (w : ℂ) (hd : dist x w ≤ r) : -r ≤ x.im-w.im ∧ x.im-w.im ≤ r := by
    apply abs_le.mp
    have hh : |x.im-w.im| ≤ dist x w := by simpa only [Complex.sub_im,dist_eq_norm] using Complex.abs_im_le_norm (x-w)
    exact hh.trans hd
  have hR1 := hRe w1 hd1
  have hR2 := hRe w2 hd2
  have hI0 := hIm w0 hd0
  have hI1 := hIm w1 hd1
  have hrx : |x.re| ≤ r := abs_le.mpr ⟨by linarith,by linarith⟩
  have hix : |x.im| ≤ r := abs_le.mpr ⟨by linarith,by linarith⟩
  have h := Complex.norm_le_abs_re_add_abs_im x
  linarith

theorem discrete_rectangle_approx_zero (f : ℕ → ℕ → ℂ) (m n : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hhor : ∀ i < m, ∀ j ≤ n, dist (f i j) (f (i+1) j) ≤ D)
    (hver : ∀ i ≤ m, ∀ j < n, dist (f i j) (f i (j+1)) ≤ D)
    (hbottom : ∀ i ≤ m, (f i 0).im < 0)
    (htop : ∀ i ≤ m, 0 ≤ (f i n).im)
    (hleft : ∀ j ≤ n, (f 0 j).re < 0)
    (hright : ∀ j ≤ n, 0 ≤ (f m j).re) :
    ∃ i ≤ m, ∃ j ≤ n, ‖f i j‖ ≤ 4*D := by
  have hb : ∀ i ≤ m, pointColor (f i 0) = 0 := by
    intro i hi
    simp [pointColor,hbottom i hi]
  have ht : ∀ i ≤ m, pointColor (f i n) ≠ 0 := by
    intro i hi hh
    exact (not_lt_of_ge (htop i hi)) (pointColor_zero hh)
  have hl : ∀ j ≤ n, pointColor (f 0 j) ≠ 2 := by
    intro j hj hh
    exact (not_le_of_gt (hleft j hj)) (pointColor_two hh).1
  have hr : ∀ j ≤ n, pointColor (f m j) ≠ 1 := by
    intro j hj hh
    exact (not_lt_of_ge (hright j hj)) (pointColor_one hh).1
  obtain ⟨i,hi,j,hj,hc⟩ := discrete_rectangle_sperner (fun i j => pointColor (f i j)) m n hb ht hl hr
  refine ⟨i,hi.le,j,hj.le,?_⟩
  have hdiag : dist (f i j) (f (i+1) (j+1)) ≤ 2*D := by
    have h := dist_triangle (f i j) (f (i+1) j) (f (i+1) (j+1))
    have h1 := hhor i hi j hj.le
    have h2 := hver (i+1) hi j hj
    linarith
  rcases hc with hc | hc
  · have hh := tricolored_norm_bound (show 0 ≤ 2*D by positivity)
      ((hhor i hi j hj.le).trans (by linarith : D ≤ 2*D)) hdiag hc
    linarith
  · have hh := tricolored_norm_bound (show 0 ≤ 2*D by positivity)
      ((hver i hi.le j hj).trans (by linarith : D ≤ 2*D)) hdiag hc
    linarith

noncomputable def repeatPath (v : ℕ → ℂ) (n : ℕ) (a : ℂ) (t : ℕ) : ℂ :=
  v (t % n) + ((t / n : ℕ) : ℂ) * a

@[simp] theorem repeatPath_zero (v : ℕ → ℂ) (n : ℕ) (a : ℂ) :
    repeatPath v n a 0 = v 0 := by simp [repeatPath]

@[simp] theorem repeatPath_multiple (v : ℕ → ℂ) {n : ℕ} (hn : 0 < n) (a : ℂ) (k : ℕ) :
    repeatPath v n a (k*n) = v 0 + (k : ℂ)*a := by simp [repeatPath,hn.ne']

theorem repeatPath_step (v : ℕ → ℂ) {n : ℕ} (hn : 0 < n) (a : ℂ)
    (hv0 : v 0 = 0) (hvn : v n = a) {D : ℝ}
    (hstep : ∀ i < n, dist (v i) (v (i+1)) ≤ D) (t : ℕ) :
    dist (repeatPath v n a t) (repeatPath v n a (t+1)) ≤ D := by
  have hr := Nat.mod_lt t hn
  have hdiv := Nat.mod_add_div t n
  by_cases hh : t % n + 1 = n
  · have ht : t+1 = (t/n+1)*n := by linarith
    rw [ht,repeatPath_multiple v hn]
    have he : repeatPath v n a t = v (t%n) + ((t/n:ℕ):ℂ)*a := rfl
    rw [he,hv0,zero_add,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm (((t/n:ℕ):ℂ)*a) a]
    rw [dist_add_right]
    simpa [hh,hvn] using hstep (t%n) hr
  · have hr' : t%n+1 < n := by omega
    have ht : t+1 = t%n+1+(t/n)*n := by linarith
    have hmod : (t+1)%n = t%n+1 := by rw [ht,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hr']
    have hquo : (t+1)/n = t/n := by rw [ht,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt hr',zero_add]
    simp only [repeatPath,hmod,hquo,dist_add_right]
    exact hstep (t%n) hr

theorem discrete_rectangle_approx_zero_rev (f : ℕ → ℕ → ℂ) (m n : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hhor : ∀ i < m, ∀ j ≤ n, dist (f i j) (f (i+1) j) ≤ D)
    (hver : ∀ i ≤ m, ∀ j < n, dist (f i j) (f i (j+1)) ≤ D)
    (hbottom : ∀ i ≤ m, 0 < (f i 0).im)
    (htop : ∀ i ≤ m, (f i n).im ≤ 0)
    (hleft : ∀ j ≤ n, (f 0 j).re < 0)
    (hright : ∀ j ≤ n, 0 ≤ (f m j).re) :
    ∃ i ≤ m, ∃ j ≤ n, ‖f i j‖ ≤ 4*D := by
  have hh : ∀ i < m, ∀ j ≤ n, dist (star (f i j)) (star (f (i+1) j)) ≤ D := by
    intro i hi j hj
    simpa only [dist_star_star] using hhor i hi j hj
  have hv : ∀ i ≤ m, ∀ j < n, dist (star (f i j)) (star (f i (j+1))) ≤ D := by
    intro i hi j hj
    simpa only [dist_star_star] using hver i hi j hj
  have hb : ∀ i ≤ m, (star (f i 0)).im < 0 := by
    intro i hi
    simpa only [Complex.star_def,Complex.conj_im,neg_lt_zero] using hbottom i hi
  have ht : ∀ i ≤ m, 0 ≤ (star (f i n)).im := by
    intro i hi
    simpa only [Complex.star_def,Complex.conj_im,neg_nonneg] using htop i hi
  obtain ⟨i,hi,j,hj,hz⟩ := discrete_rectangle_approx_zero (fun i j => star (f i j)) m n
    hD hh hv hb ht (by simpa only [Complex.star_def,Complex.conj_re] using hleft)
      (by simpa only [Complex.star_def,Complex.conj_re] using hright)
  exact ⟨i,hi,j,hj,by simpa only [norm_star] using hz⟩

theorem path_difference_cover (v u : ℕ → ℂ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (a b : ℂ) (hv0 : v 0 = 0) (hu0 : u 0 = 0) (hvn : v n = a) (hum : u m = b)
    (ha : 0 < a.re) (hai : a.im = 0) (hb : 0 < b.im) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i < n, dist (v i) (v (i+1)) ≤ D)
    (hu : ∀ j < m, dist (u j) (u (j+1)) ≤ D) (w : ℂ) :
    ∃ i < n, ∃ j < m, ∃ s t : ℤ,
      ‖v i-u j+(s:ℂ)*a+(t:ℂ)*b-w‖ ≤ 4*D := by
  let H : ℝ := (∑ i ∈ Finset.range n, ‖v i‖) + (∑ j ∈ Finset.range m, ‖u j‖) + ‖w‖
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hvb (i : ℕ) : ‖v (i%n)‖ ≤ ∑ k ∈ Finset.range n, ‖v k‖ :=
    Finset.single_le_sum (fun k _ => norm_nonneg (v k)) (Finset.mem_range.mpr (Nat.mod_lt i hn))
  have hub (j : ℕ) : ‖u (j%m)‖ ≤ ∑ k ∈ Finset.range m, ‖u k‖ :=
    Finset.single_le_sum (fun k _ => norm_nonneg (u k)) (Finset.mem_range.mpr (Nat.mod_lt j hm))
  have herr (i j : ℕ) : ‖v (i%n)-u (j%m)-w‖ ≤ H := by
    have h1 := norm_sub_le (v (i%n)) (u (j%m))
    have h2 := norm_sub_le (v (i%n)-u (j%m)) w
    dsimp [H]
    linarith [hvb i,hub j]
  have hrerr (i j : ℕ) : -H ≤ (v (i%n)-u (j%m)-w).re ∧
      (v (i%n)-u (j%m)-w).re ≤ H :=
    abs_le.mp ((Complex.abs_re_le_norm _).trans (herr i j))
  have hierr (i j : ℕ) : -H ≤ (v (i%n)-u (j%m)-w).im ∧
      (v (i%n)-u (j%m)-w).im ≤ H :=
    abs_le.mp ((Complex.abs_im_le_norm _).trans (herr i j))
  obtain ⟨N,hN⟩ := exists_nat_gt (H/b.im)
  have hN' : H < (N:ℝ)*b.im := (div_lt_iff₀ hb).mp hN
  obtain ⟨M,hM⟩ := exists_nat_gt ((H+(N:ℝ)*|b.re|)/a.re)
  have hM' : H+(N:ℝ)*|b.re| < (M:ℝ)*a.re := (div_lt_iff₀ ha).mp hM
  let f (i j : ℕ) : ℂ := repeatPath v n a i-repeatPath u m b j-(M:ℂ)*a+(N:ℂ)*b-w
  have hf (i j : ℕ) : f i j = v (i%n)-u (j%m)-w +
      (((i/n:ℕ):ℂ)-(M:ℂ))*a + ((N:ℂ)-((j/m:ℕ):ℂ))*b := by
    dsimp [f,repeatPath]
    ring
  have hfr (i j : ℕ) : (f i j).re = (v (i%n)-u (j%m)-w).re +
      (((i/n:ℕ):ℝ)-(M:ℝ))*a.re + ((N:ℝ)-((j/m:ℕ):ℝ))*b.re := by
    rw [hf]
    simp
  have hfi (i j : ℕ) : (f i j).im = (v (i%n)-u (j%m)-w).im +
      ((N:ℝ)-((j/m:ℕ):ℝ))*b.im := by
    rw [hf]
    simp [hai]
  have hhor (i : ℕ) (_ : i < 2*M*n) (j : ℕ) (_ : j ≤ 2*N*m) :
      dist (f i j) (f (i+1) j) ≤ D := by
    simpa only [f,dist_sub_right,dist_add_right] using repeatPath_step v hn a hv0 hvn hv i
  have hver (i : ℕ) (_ : i ≤ 2*M*n) (j : ℕ) (_ : j < 2*N*m) :
      dist (f i j) (f i (j+1)) ≤ D := by
    simpa only [f,dist_sub_right,dist_add_right,dist_sub_left] using repeatPath_step u hm b hu0 hum hu j
  have hbottom (i : ℕ) (_ : i ≤ 2*M*n) : 0 < (f i 0).im := by
    rw [hfi]
    simpa only [Nat.zero_div,Nat.cast_zero,sub_zero] using (show
      0 < (v (i%n)-u (0%m)-w).im+(N:ℝ)*b.im by linarith [(hierr i 0).1])
  have htop (i : ℕ) (_ : i ≤ 2*M*n) : (f i (2*N*m)).im ≤ 0 := by
    rw [hfi,Nat.mul_div_cancel _ hm,Nat.cast_mul,Nat.cast_ofNat]
    linarith [(hierr i (2*N*m)).2]
  have hcoef (j : ℕ) (hj : j ≤ 2*N*m) :
      |(N:ℝ)-((j/m:ℕ):ℝ)| ≤ N := by
    have hq : j/m ≤ 2*N := (Nat.div_le_div_right hj).trans_eq (Nat.mul_div_cancel _ hm)
    have hqr : ((j/m:ℕ):ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hq
    exact abs_le.mpr ⟨by linarith,by linarith [Nat.cast_nonneg (α := ℝ) (j/m)]⟩
  have hprod (j : ℕ) (hj : j ≤ 2*N*m) :
      -(N:ℝ)*|b.re| ≤ ((N:ℝ)-((j/m:ℕ):ℝ))*b.re ∧
      ((N:ℝ)-((j/m:ℕ):ℝ))*b.re ≤ (N:ℝ)*|b.re| := by
    have hh : |((N:ℝ)-((j/m:ℕ):ℝ))*b.re| ≤ (N:ℝ)*|b.re| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hcoef j hj) (abs_nonneg _)
    simpa only [neg_mul] using abs_le.mp hh
  have hleft (j : ℕ) (hj : j ≤ 2*N*m) : (f 0 j).re < 0 := by
    rw [hfr]
    simp only [Nat.zero_div,Nat.cast_zero,zero_sub]
    linarith [(hrerr 0 j).2,(hprod j hj).2]
  have hright (j : ℕ) (hj : j ≤ 2*N*m) : 0 ≤ (f (2*M*n) j).re := by
    rw [hfr,Nat.mul_div_cancel _ hn,Nat.cast_mul,Nat.cast_ofNat]
    linarith [(hrerr (2*M*n) j).1,(hprod j hj).1]
  obtain ⟨i,_,j,_,hz⟩ := discrete_rectangle_approx_zero_rev f (2*M*n) (2*N*m)
    hD hhor hver hbottom htop hleft hright
  refine ⟨i%n,Nat.mod_lt i hn,j%m,Nat.mod_lt j hm,((i/n:ℕ):ℤ)-(M:ℤ),(N:ℤ)-((j/m:ℕ):ℤ),?_⟩
  convert hz using 1
  rw [hf]
  simp only [Int.cast_sub,Int.cast_natCast]
  congr 1
  ring

theorem path_difference_cover_horizontal (v u : ℕ → ℂ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (a b : ℂ) (hv0 : v 0 = 0) (hu0 : u 0 = 0) (hvn : v n = a) (hum : u m = b)
    (ha : 0 < a.re) (hai : a.im = 0) (hb : b.im ≠ 0) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i < n, dist (v i) (v (i+1)) ≤ D)
    (hu : ∀ j < m, dist (u j) (u (j+1)) ≤ D) (w : ℂ) :
    ∃ i < n, ∃ j < m, ∃ s t : ℤ,
      ‖v i-u j+(s:ℂ)*a+(t:ℂ)*b-w‖ ≤ 4*D := by
  rcases hb.lt_or_gt with hb | hb
  · have hzv : (fun i => star (v i)) 0 = 0 := by simp [hv0]
    have hzu : (fun i => star (u i)) 0 = 0 := by simp [hu0]
    have hva : (fun i => star (v i)) n = star a := by simp only [hvn]
    have hub : (fun i => star (u i)) m = star b := by simp only [hum]
    have hbr : 0 < (star b).im := by simpa using hb
    have hv' : ∀ i < n, dist (star (v i)) (star (v (i+1))) ≤ D := by simpa using hv
    have hu' : ∀ j < m, dist (star (u j)) (star (u (j+1))) ≤ D := by simpa using hu
    obtain ⟨i,hi,j,hj,s,t,hh⟩ := path_difference_cover (fun i => star (v i))
      (fun j => star (u j)) hn hm (star a) (star b) hzv hzu hva hub
      (by simpa using ha) (by simpa using hai) hbr hD hv' hu' (star w)
    refine ⟨i,hi,j,hj,s,t,?_⟩
    have he : ‖star (v i-u j+(s:ℂ)*a+(t:ℂ)*b-w)‖ ≤ 4*D := by
      simpa only [star_sub,star_add,star_mul,star_intCast,mul_comm] using hh
    simpa only [norm_star] using he
  · exact path_difference_cover v u hn hm a b hv0 hu0 hvn hum ha hai hb hD hv hu w

theorem path_difference_cover_general (v u : ℕ → ℂ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (a b : ℂ) (hv0 : v 0 = 0) (hu0 : u 0 = 0) (hvn : v n = a) (hum : u m = b)
    (ha : a ≠ 0) (hb : (b/a).im ≠ 0) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i < n, dist (v i) (v (i+1)) ≤ D)
    (hu : ∀ j < m, dist (u j) (u (j+1)) ≤ D) (w : ℂ) :
    ∃ i < n, ∃ j < m, ∃ s t : ℤ,
      ‖v i-u j+(s:ℂ)*a+(t:ℂ)*b-w‖ ≤ 4*D := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hv' : ∀ i < n, dist (v i/a) (v (i+1)/a) ≤ D/‖a‖ := by
    intro i hi
    simp only [dist_eq_norm,← sub_div,norm_div]
    exact div_le_div_of_nonneg_right (by simpa only [dist_eq_norm] using hv i hi) hna.le
  have hu' : ∀ j < m, dist (u j/a) (u (j+1)/a) ≤ D/‖a‖ := by
    intro j hj
    simp only [dist_eq_norm,← sub_div,norm_div]
    exact div_le_div_of_nonneg_right (by simpa only [dist_eq_norm] using hu j hj) hna.le
  obtain ⟨i,hi,j,hj,s,t,hh⟩ := path_difference_cover_horizontal (fun i => v i/a)
    (fun j => u j/a) hn hm 1 (b/a) (by simp [hv0]) (by simp [hu0])
    (by simp [hvn,ha]) (by simp [hum]) (by norm_num) (by simp) hb
    (by positivity : 0 ≤ D/‖a‖) hv' hu' (w/a)
  refine ⟨i,hi,j,hj,s,t,?_⟩
  have he : v i/a-u j/a+(s:ℂ)*1+(t:ℂ)*(b/a)-w/a =
      (v i-u j+(s:ℂ)*a+(t:ℂ)*b-w)/a := by field_simp
  rw [he,norm_div] at hh
  have hh' := (div_le_iff₀ hna).mp hh
  calc
    _ ≤ 4 * (D/‖a‖) * ‖a‖ := hh'
    _ = 4*D := by field_simp

end

def latticeCoords : GaussianInt ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun z := ![z.re,z.im]
  invFun v := ⟨v 0,v 1⟩
  left_inv z := by ext <;> rfl
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' z w := by ext i; fin_cases i <;> rfl
  map_smul' c z := by
    ext i
    fin_cases i <;> simp [zsmul_eq_mul]

noncomputable def latticeBasis : Module.Basis (Fin 2) ℤ GaussianInt :=
  (Pi.basisFun ℤ (Fin 2)).map latticeCoords.symm

noncomputable instance : Module.Free ℤ GaussianInt := Module.Free.of_basis latticeBasis
instance : Module.Finite ℤ GaussianInt := Module.Finite.of_basis latticeBasis

noncomputable def twoVectorMap (a b : GaussianInt) : GaussianInt →ₗ[ℤ] GaussianInt :=
  Matrix.toLin latticeBasis latticeBasis !![a.re,b.re; a.im,b.im]

@[simp] theorem twoVectorMap_apply (a b z : GaussianInt) :
    twoVectorMap a b z = z.re • a + z.im • b := by
  apply latticeCoords.injective
  change latticeBasis.repr (twoVectorMap a b z) = latticeCoords (z.re • a+z.im • b)
  rw [twoVectorMap,Matrix.toLin_apply]
  simp only [map_sum,map_smul,Module.Basis.repr_self]
  ext i
  fin_cases i <;> simp [latticeCoords,latticeBasis,zsmul_eq_mul,Fin.sum_univ_two,Pi.basisFun_repr,Matrix.vecHead,Matrix.vecTail] <;> ring

@[simp] theorem twoVectorMap_det (a b : GaussianInt) :
    LinearMap.det (twoVectorMap a b) = a.re*b.im-a.im*b.re := by
  rw [← LinearMap.det_toMatrix latticeBasis,twoVectorMap,LinearMap.toMatrix_toLin]
  simp [Matrix.det_fin_two,mul_comm]

theorem twoVectorMap_injective {a b : GaussianInt} (h : a.re*b.im-a.im*b.re ≠ 0) :
    Function.Injective (twoVectorMap a b) := by
  intro z w hzw
  have h1 := congrArg Zsqrtd.re hzw
  have h2 := congrArg Zsqrtd.im hzw
  simp only [twoVectorMap_apply,zsmul_eq_mul,Zsqrtd.re_add,Zsqrtd.im_add,
    Zsqrtd.re_smul,Zsqrtd.im_smul] at h1 h2
  have hr : (a.re*b.im-a.im*b.re)*(z.re-w.re) = 0 := by linear_combination b.im*h1-b.re*h2
  have hi : (a.re*b.im-a.im*b.re)*(z.im-w.im) = 0 := by linear_combination a.re*h2-a.im*h1
  ext
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hr).resolve_left h)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left h)

theorem twoVectorMap_quotient_card {a b : GaussianInt} (h : a.re*b.im-a.im*b.re ≠ 0) :
    Nat.card (GaussianInt ⧸ (twoVectorMap a b).range) = (a.re*b.im-a.im*b.re).natAbs := by
  have hh := Submodule.natAbs_det_equiv (twoVectorMap a b).range
    (LinearEquiv.ofInjective (twoVectorMap a b) (twoVectorMap_injective h))
  have he : (twoVectorMap a b).range.subtype ∘ₗ
      AddMonoidHom.toIntLinearMap ((LinearEquiv.ofInjective (twoVectorMap a b)
        (twoVectorMap_injective h)) : GaussianInt →+ (twoVectorMap a b).range) = twoVectorMap a b := by
    ext z <;> rfl
  rw [he,twoVectorMap_det] at hh
  exact hh.symm

noncomputable def latticeBall (D : ℝ) : Finset GaussianInt :=
  (finite_dist_le 0 D).toFinset

@[simp] theorem mem_latticeBall (D : ℝ) (z : GaussianInt) :
    z ∈ latticeBall D ↔ ‖(z:ℂ)‖ ≤ D := by simp [latticeBall]

theorem complex_div_im_ne_zero {a b : GaussianInt} (h : a.re*b.im-a.im*b.re ≠ 0) :
    ((b:ℂ)/(a:ℂ)).im ≠ 0 := by
  have ha : a ≠ 0 := by intro hh; simp [hh] at h
  have hac : (a:ℂ) ≠ 0 := by simpa using ha
  have hn : Complex.normSq (a:ℂ) ≠ 0 := (Complex.normSq_pos.mpr hac).ne'
  rw [Complex.div_im,← sub_div]
  intro hh
  have hh' := (div_eq_zero_iff.mp hh).resolve_right hn
  have hz : (a.re:ℝ)*(b.im:ℝ)-(a.im:ℝ)*(b.re:ℝ) = 0 := by
    simpa only [← GaussianInt.intCast_re,← GaussianInt.intCast_im,mul_comm] using hh'
  apply h
  exact_mod_cast hz

theorem lattice_path_difference_cover (v u : ℕ → GaussianInt) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (a b : GaussianInt)
    (hv0 : v 0 = 0) (hu0 : u 0 = 0) (hvn : v n = a) (hum : u m = b)
    (hab : a.re*b.im-a.im*b.re ≠ 0) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i < n, dist (v i:ℂ) (v (i+1):ℂ) ≤ D)
    (hu : ∀ j < m, dist (u j:ℂ) (u (j+1):ℂ) ≤ D) (w : GaussianInt) :
    ∃ i < n, ∃ j < m, ∃ s t : ℤ,
      ‖((v i-u j+(s:GaussianInt)*a+(t:GaussianInt)*b-w:GaussianInt):ℂ)‖ ≤ 4*D := by
  have ha : a ≠ 0 := by intro hh; simp [hh] at hab
  obtain ⟨i,hi,j,hj,s,t,hh⟩ := path_difference_cover_general
    (fun i => (v i:ℂ)) (fun j => (u j:ℂ)) hn hm (a:ℂ) (b:ℂ)
    (by simp [hv0]) (by simp [hu0]) (by simp [hvn]) (by simp [hum])
    (by simpa using ha) (complex_div_im_ne_zero hab) hD hv hu (w:ℂ)
  exact ⟨i,hi,j,hj,s,t,by simpa using hh⟩

theorem lattice_path_difference_card (v u : ℕ → GaussianInt) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (a b : GaussianInt)
    (hv0 : v 0 = 0) (hu0 : u 0 = 0) (hvn : v n = a) (hum : u m = b)
    (hab : a.re*b.im-a.im*b.re ≠ 0) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i < n, dist (v i:ℂ) (v (i+1):ℂ) ≤ D)
    (hu : ∀ j < m, dist (u j:ℂ) (u (j+1):ℂ) ≤ D)
    (E : Finset GaussianInt) (hE : ∀ i < n, ∀ j < m, v i-u j ∈ E) :
    (a.re*b.im-a.im*b.re).natAbs ≤ E.card*(latticeBall (4*D)).card := by
  classical
  let Q := (twoVectorMap a b).range
  have hcard : Nat.card (GaussianInt ⧸ Q) = (a.re*b.im-a.im*b.re).natAbs :=
    twoVectorMap_quotient_card hab
  have : Finite (GaussianInt ⧸ Q) := Nat.finite_of_card_ne_zero (by rw [hcard]; simpa using hab)
  let : Fintype (GaussianInt ⧸ Q) := Fintype.ofFinite _
  let F : E × (latticeBall (4*D)) → GaussianInt ⧸ Q :=
    fun x => Q.mkQ (x.1.val+x.2.val)
  have hf : Function.Surjective F := by
    intro q
    obtain ⟨w,rfl⟩ := Q.mkQ_surjective q
    obtain ⟨i,hi,j,hj,s,t,hh⟩ := lattice_path_difference_cover v u hn hm a b hv0 hu0 hvn hum hab hD hv hu w
    let r : GaussianInt := -(v i-u j+(s:GaussianInt)*a+(t:GaussianInt)*b-w)
    have hr : r ∈ latticeBall (4*D) := by
      rw [mem_latticeBall]
      dsimp only [r]
      rw [map_neg,norm_neg]
      exact hh
    refine ⟨(⟨v i-u j,hE i hi j hj⟩,⟨r,hr⟩),?_⟩
    apply (Submodule.Quotient.eq Q).mpr
    change (v i-u j)+r-w ∈ (twoVectorMap a b).range
    refine ⟨⟨-s,-t⟩,?_⟩
    rw [twoVectorMap_apply]
    change (-s) • a + (-t) • b = _
    simp only [zsmul_eq_mul,Int.cast_neg]
    dsimp [r]
    ring
  have hh := Fintype.card_le_of_surjective F hf
  have hQ : Fintype.card (GaussianInt ⧸ Q) = (a.re*b.im-a.im*b.re).natAbs := by
    rw [← Nat.card_eq_fintype_card,hcard]
  simpa only [Fintype.card_prod,Fintype.card_coe,hQ] using hh

theorem lattice_norm_ge_one {z : GaussianInt} (hz : z ≠ 0) : 1 ≤ ‖(z:ℂ)‖ := by
  have hi : 1 ≤ z.norm := by have := GaussianInt.norm_pos.mpr hz; omega
  have hr : (1:ℝ) ≤ (z.norm:ℝ) := by exact_mod_cast hi
  rw [GaussianInt.intCast_real_norm,Complex.normSq_eq_norm_sq] at hr
  nlinarith [norm_nonneg (z:ℂ)]

theorem lattice_dist_ge_one {z w : GaussianInt} (h : z ≠ w) :
    1 ≤ dist (z:ℂ) (w:ℂ) := by
  simpa only [map_sub,dist_eq_norm] using lattice_norm_ge_one (sub_ne_zero.mpr h)

noncomputable def latticePixel (e c : ℂ) (z : GaussianInt) : ℤ × ℤ :=
  (⌊2*(e*((z:ℂ)-c)).re⌋,⌊2*(e*((z:ℂ)-c)).im⌋)

theorem abs_sub_lt_half_of_pixel_eq {x y : ℝ} (h : ⌊2*x⌋ = ⌊2*y⌋) : |x-y| < 1/2 := by
  have h1 := Int.floor_le (2*x)
  have h2 := Int.lt_floor_add_one (2*x)
  have h3 := Int.floor_le (2*y)
  have h4 := Int.lt_floor_add_one (2*y)
  rw [h] at h1 h2
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

theorem latticePixel_injective {e : ℂ} (he : ‖e‖ = 1) (c : ℂ) :
    Function.Injective (latticePixel e c) := by
  intro z w h
  have hr := abs_sub_lt_half_of_pixel_eq (congrArg Prod.fst h)
  have hi := abs_sub_lt_half_of_pixel_eq (congrArg Prod.snd h)
  have hn : ‖e*((z:ℂ)-c)-e*((w:ℂ)-c)‖ < 1 := by
    have hh := Complex.norm_le_abs_re_add_abs_im (e*((z:ℂ)-c)-e*((w:ℂ)-c))
    simp only [Complex.sub_re,Complex.sub_im] at hh
    change |(e*((z:ℂ)-c)).re-(e*((w:ℂ)-c)).re| < 1/2 at hr
    change |(e*((z:ℂ)-c)).im-(e*((w:ℂ)-c)).im| < 1/2 at hi
    linarith
  have heq : e*((z:ℂ)-c)-e*((w:ℂ)-c) = e*((z:ℂ)-(w:ℂ)) := by ring
  rw [heq,norm_mul,he,one_mul] at hn
  by_contra hne
  exact (not_lt_of_ge (lattice_dist_ge_one hne)) (by simpa only [dist_eq_norm] using hn)

theorem lattice_rectangle_card (E : Finset GaussianInt) {e c : ℂ} (he : ‖e‖ = 1)
    {R W : ℝ} (hR : 1 ≤ R) (hW : 1 ≤ W)
    (hE : ∀ z ∈ E, 0 ≤ (e*((z:ℂ)-c)).re ∧ (e*((z:ℂ)-c)).re ≤ R ∧
      |(e*((z:ℂ)-c)).im| ≤ W) :
    (E.card:ℝ) ≤ 18*R*W := by
  classical
  let B : Finset (ℤ × ℤ) := Finset.Icc 0 ⌊2*R⌋ ×ˢ Finset.Icc ⌊-2*W⌋ ⌊2*W⌋
  have hb : E.image (latticePixel e c) ⊆ B := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hz0,hzR,hzW⟩ := hE z hz
    have hzw := abs_le.mp hzW
    simp only [B,Finset.mem_product,Finset.mem_Icc,latticePixel]
    refine ⟨⟨?_,Int.floor_mono (by linarith)⟩,
      ⟨Int.floor_mono (by linarith),Int.floor_mono (by linarith)⟩⟩
    exact Int.floor_nonneg.mpr (by linarith)
  have hcard : E.card ≤ B.card := by
    rw [← Finset.card_image_iff.mpr (latticePixel_injective he c).injOn]
    exact Finset.card_le_card hb
  have hR0 : (0:ℤ) ≤ ⌊2*R⌋+1 := by
    have hh : (0:ℤ) ≤ ⌊2*R⌋ := Int.floor_nonneg.mpr (by linarith)
    omega
  have hW0 : ⌊-2*W⌋ ≤ ⌊2*W⌋+1 := by
    have hh : ⌊-2*W⌋ ≤ ⌊2*W⌋ := Int.floor_mono (by linarith)
    omega
  have hcr : ((Finset.Icc (0:ℤ) ⌊2*R⌋).card:ℝ) = (⌊2*R⌋:ℝ)+1 := by
    have h := Int.card_Icc_of_le 0 ⌊2*R⌋ hR0
    simp only [sub_zero] at h
    exact_mod_cast h
  have hcw : ((Finset.Icc ⌊-2*W⌋ ⌊2*W⌋).card:ℝ) = (⌊2*W⌋:ℝ)+1-(⌊-2*W⌋:ℝ) := by
    exact_mod_cast Int.card_Icc_of_le ⌊-2*W⌋ ⌊2*W⌋ hW0
  have hrb : ((Finset.Icc (0:ℤ) ⌊2*R⌋).card:ℝ) ≤ 3*R := by
    rw [hcr]
    linarith [Int.floor_le (2*R)]
  have hwb : ((Finset.Icc ⌊-2*W⌋ ⌊2*W⌋).card:ℝ) ≤ 6*W := by
    rw [hcw]
    linarith [Int.floor_le (2*W),Int.lt_floor_add_one (-2*W)]
  have hh : (E.card:ℝ) ≤ ((Finset.Icc (0:ℤ) ⌊2*R⌋).card:ℝ)*
      ((Finset.Icc ⌊-2*W⌋ ⌊2*W⌋).card:ℝ) := by
    dsimp only [B] at hcard
    rw [Finset.card_product] at hcard
    exact_mod_cast hcard
  calc
    (E.card:ℝ) ≤ _ := hh
    _ ≤ (3*R)*(6*W) := mul_le_mul hrb hwb (Nat.cast_nonneg _) (by linarith)
    _ = 18*R*W := by ring

end GaussianMoat

end OAI
end
end

section
section
namespace OAI

namespace GaussianMoat

noncomputable def walkSegment (z : ℕ → GaussianInt) (n : ℕ) : Finset GaussianInt :=
  (Finset.range (n+1)).image z

noncomputable def differences (E : Finset GaussianInt) : Finset GaussianInt :=
  (E ×ˢ E).image (fun p => p.1-p.2)

@[simp] theorem mem_walkSegment (z : ℕ → GaussianInt) (n : ℕ) (w : GaussianInt) :
    w ∈ walkSegment z n ↔ ∃ i ≤ n, z i = w := by
  simp [walkSegment,Finset.mem_image]

@[simp] theorem mem_differences (E : Finset GaussianInt) (w : GaussianInt) :
    w ∈ differences E ↔ ∃ a ∈ E, ∃ b ∈ E, a-b = w := by
  simp [differences,Finset.mem_image,Prod.exists,and_assoc]

theorem card_le_card_differences {E : Finset GaussianInt} (hE : E.Nonempty) :
    E.card ≤ (differences E).card := by
  classical
  obtain ⟨a,ha⟩ := hE
  have hs : E.image (fun b => b-a) ⊆ differences E := by
    intro w hw
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hw
    exact mem_differences E (b-a) |>.mpr ⟨b,hb,a,ha,rfl⟩
  have hi : Function.Injective (fun b : GaussianInt => b-a) := sub_left_injective
  rw [← Finset.card_image_of_injective E hi]
  exact Finset.card_le_card hs

theorem walkSegment_dist_le (z : ℕ → GaussianInt) {n : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (hz : ∀ i < n, dist (z i:ℂ) (z (i+1):ℂ) ≤ D) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) :
    dist (z i:ℂ) (z j:ℂ) ≤ D*n := by
  wlog hij : i ≤ j generalizing i j
  · rw [dist_comm]
    exact this hj hi (by omega)
  have h := dist_le_Ico_sum_of_dist_le (f := fun k => (z k:ℂ)) hij
    (d := fun _ => D) (fun {k} _ hk => hz k (lt_of_lt_of_le hk hj))
  simp only [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul] at h
  calc
    dist (z i:ℂ) (z j:ℂ) ≤ (j-i:ℕ)*D := h
    _ ≤ (n:ℝ)*D := mul_le_mul_of_nonneg_right (by exact_mod_cast (show j-i ≤ n by omega)) hD
    _ = D*n := mul_comm _ _

def joinedPath (z : ℕ → GaussianInt) (t : ℕ) (i : ℕ) : GaussianInt :=
  z (Nat.dist t i)-z t

@[simp] theorem joinedPath_zero (z : ℕ → GaussianInt) (t : ℕ) : joinedPath z t 0 = 0 := by
  simp [joinedPath,Nat.dist]

@[simp] theorem joinedPath_end (z : ℕ → GaussianInt) (t s : ℕ) :
    joinedPath z t (t+s) = z s-z t := by simp [joinedPath,Nat.dist]

theorem joinedPath_step (z : ℕ → GaussianInt) {n t s : ℕ} (ht : t ≤ n) (hs : s ≤ n)
    {D : ℝ} (hz : ∀ i < n, dist (z i:ℂ) (z (i+1):ℂ) ≤ D) :
    ∀ i < t+s, dist (joinedPath z t i:ℂ) (joinedPath z t (i+1):ℂ) ≤ D := by
  intro i hi
  simp only [joinedPath,map_sub,dist_sub_right]
  by_cases hit : i < t
  · have he : Nat.dist t i = Nat.dist t (i+1)+1 := by simp only [Nat.dist]; omega
    rw [he,dist_comm]
    exact hz _ (by simp only [Nat.dist]; omega)
  · have he : Nat.dist t (i+1) = Nat.dist t i+1 := by simp only [Nat.dist]; omega
    rw [he]
    exact hz _ (by simp only [Nat.dist]; omega)

theorem differences_card_of_triangle (z : ℕ → GaussianInt) {n t s u : ℕ}
    (ht : t ≤ n) (hs : s ≤ n) (hu : u ≤ n) {D : ℝ} (hD : 0 ≤ D)
    (hz : ∀ i < n, dist (z i:ℂ) (z (i+1):ℂ) ≤ D)
    (hab : (z s-z t).re*(z u-z t).im-(z s-z t).im*(z u-z t).re ≠ 0) :
    ((z s-z t).re*(z u-z t).im-(z s-z t).im*(z u-z t).re).natAbs ≤
      (differences (walkSegment z n)).card * (latticeBall (4*D)).card := by
  have hts : 0 < t+s := by
    by_contra hh
    have ht0 : t=0 := by omega
    have hs0 : s=0 := by omega
    simp [ht0,hs0] at hab
  have htu : 0 < t+u := by
    by_contra hh
    have ht0 : t=0 := by omega
    have hu0 : u=0 := by omega
    simp [ht0,hu0] at hab
  apply lattice_path_difference_card (joinedPath z t) (joinedPath z t) hts htu
    (z s-z t) (z u-z t) (joinedPath_zero z t) (joinedPath_zero z t)
    (joinedPath_end z t s) (joinedPath_end z t u) hab hD
    (joinedPath_step z ht hs hz) (joinedPath_step z ht hu hz)
  intro i hi j hj
  apply (mem_differences _ _).mpr
  refine ⟨z (Nat.dist t i),(mem_walkSegment _ _ _).mpr ⟨_,?_,rfl⟩,
    z (Nat.dist t j),(mem_walkSegment _ _ _).mpr ⟨_,?_,rfl⟩,?_⟩
  · simp only [Nat.dist]; omega
  · simp only [Nat.dist]; omega
  · simp only [joinedPath]; ring

noncomputable def diameterRotation (a : ℂ) : ℂ := star a / (‖a‖:ℂ)

theorem diameterRotation_norm {a : ℂ} (ha : a ≠ 0) : ‖diameterRotation a‖ = 1 := by
  simp [diameterRotation,Complex.norm_real,norm_ne_zero_iff.mpr ha]

theorem diameterRotation_mul (a : ℂ) : diameterRotation a*a = (‖a‖:ℂ) := by
  by_cases ha : a=0
  · simp [ha,diameterRotation]
  have hn : (‖a‖:ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ha
  have hm : star a*a = (‖a‖:ℂ)^2 := Complex.conj_mul' a
  rw [diameterRotation,div_mul_eq_mul_div,hm]
  field_simp

theorem diameter_rectangle {a v : ℂ} (ha : a ≠ 0) (hv : ‖v‖ ≤ ‖a‖)
    (hva : ‖v-a‖ ≤ ‖a‖) :
    0 ≤ (diameterRotation a*v).re ∧ (diameterRotation a*v).re ≤ ‖a‖ ∧
      |(diameterRotation a*v).im| ≤ ‖a‖ := by
  let u := diameterRotation a*v
  have hn : ‖u‖ ≤ ‖a‖ := by simpa [u,norm_mul,diameterRotation_norm ha] using hv
  have hna : ‖u-(‖a‖:ℂ)‖ ≤ ‖a‖ := by
    rw [← diameterRotation_mul a,← mul_sub]
    simpa [norm_mul,diameterRotation_norm ha] using hva
  have hr := Complex.abs_re_le_norm u
  have hi := Complex.abs_im_le_norm u
  have hra := Complex.abs_re_le_norm (u-(‖a‖:ℂ))
  simp only [Complex.sub_re,Complex.ofReal_re] at hra
  have hl := (abs_le.mp (hra.trans hna)).1
  exact ⟨by dsimp [u] at *; linarith, (le_abs_self u.re).trans (hr.trans hn), hi.trans hn⟩

theorem diameter_height (a b : GaussianInt) :
    |((a.re*b.im-a.im*b.re:ℤ):ℝ)| =
      ‖(a:ℂ)‖*|(diameterRotation (a:ℂ)*(b:ℂ)).im| := by
  by_cases ha : a=0
  · simp [ha,diameterRotation]
  have hna : ‖(a:ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (by simpa using ha)
  have he : (diameterRotation (a:ℂ)*(b:ℂ)).im =
      ((a.re:ℝ)*(b.im:ℝ)-(a.im:ℝ)*(b.re:ℝ))/‖(a:ℂ)‖ := by
    simp only [diameterRotation,div_mul_eq_mul_div,Complex.div_ofReal_im,
      Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
      ← GaussianInt.intCast_re,← GaussianInt.intCast_im]
    ring
  rw [he,abs_div,abs_of_nonneg (norm_nonneg (a:ℂ))]
  push_cast
  field_simp

theorem walk_many_differences (z : ℕ → GaussianInt) {n : ℕ} (hn : 1 ≤ n)
    (hinj : Function.Injective z) {D : ℝ} (hD : 1 ≤ D)
    (hz : ∀ i < n, dist (z i:ℂ) (z (i+1):ℂ) ≤ D) :
    ∃ (R W : ℝ) (e c : ℂ), 1 ≤ W ∧ W ≤ R ∧ ‖e‖ = 1 ∧
      (∀ p ∈ walkSegment z n, 0 ≤ (e*((p:ℂ)-c)).re ∧
        (e*((p:ℂ)-c)).re ≤ R ∧ |(e*((p:ℂ)-c)).im| ≤ W) ∧
      (n:ℝ) ≤ 18*(R*W) ∧ R*W ≤ D^2*(n:ℝ)^2 ∧
      R*W ≤ max D ((latticeBall (4*D)).card:ℝ)*(differences (walkSegment z n)).card := by
  classical
  let I := Finset.range (n+1)
  have hI : I.Nonempty := ⟨0,by simp [I]⟩
  obtain ⟨⟨t,s⟩,hts,hmax⟩ := Finset.exists_max_image (I ×ˢ I)
    (fun q => dist (z q.1:ℂ) (z q.2:ℂ)) (hI.product hI)
  have ht : t ≤ n := by simpa [I] using (Finset.mem_product.mp hts).1
  have hs : s ≤ n := by simpa [I] using (Finset.mem_product.mp hts).2
  let a := z s-z t
  let R := ‖(a:ℂ)‖
  have hdiam : ∀ i ≤ n, ∀ j ≤ n, dist (z i:ℂ) (z j:ℂ) ≤ R := by
    intro i hi j hj
    have h := hmax (i,j) (by simp [I,hi,hj])
    simpa [R,a,map_sub,← dist_eq_norm,dist_comm] using h
  have hR : 1 ≤ R := (lattice_dist_ge_one (hinj.ne (by omega : 0 ≠ 1))).trans (hdiam 0 (by omega) 1 hn)
  have ha : a ≠ 0 := by intro hh; simp [R,hh] at hR; linarith
  have hac : (a:ℂ) ≠ 0 := by simpa using ha
  let e := diameterRotation (a:ℂ)
  let c := (z t:ℂ)
  have he : ‖e‖ = 1 := diameterRotation_norm hac
  have hr : ∀ i ≤ n, 0 ≤ (e*((z i:ℂ)-c)).re ∧
      (e*((z i:ℂ)-c)).re ≤ R ∧ |(e*((z i:ℂ)-c)).im| ≤ R := by
    intro i hi
    have hv : ‖(z i:ℂ)-c‖ ≤ ‖(a:ℂ)‖ := by simpa only [← dist_eq_norm] using hdiam i hi t ht
    have hva : ‖((z i:ℂ)-c)-(a:ℂ)‖ ≤ ‖(a:ℂ)‖ := by
      have hh : ((z i:ℂ)-c)-(a:ℂ) = (z i:ℂ)-(z s:ℂ) := by simp [a,c]
      rw [hh,← dist_eq_norm]
      exact hdiam i hi s hs
    exact diameter_rectangle hac hv hva
  obtain ⟨u,hu,humax⟩ := Finset.exists_max_image I
    (fun i => |(e*((z i:ℂ)-c)).im|) hI
  have hu' : u ≤ n := by simpa [I] using hu
  let W := max 1 |(e*((z u:ℂ)-c)).im|
  have hW : 1 ≤ W := le_max_left _ _
  have hWR : W ≤ R := max_le hR (hr u hu').2.2
  have hrect : ∀ p ∈ walkSegment z n, 0 ≤ (e*((p:ℂ)-c)).re ∧
      (e*((p:ℂ)-c)).re ≤ R ∧ |(e*((p:ℂ)-c)).im| ≤ W := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := (mem_walkSegment _ _ _).mp hp
    exact ⟨(hr i hi).1,(hr i hi).2.1,(humax i (by simpa [I] using hi)).trans (le_max_right _ _)⟩
  have hcard : (walkSegment z n).card = n+1 := by
    rw [walkSegment,Finset.card_image_of_injective _ hinj,Finset.card_range]
  have hcount : (n:ℝ)+1 ≤ 18*R*W := by
    have h := lattice_rectangle_card (walkSegment z n) he hR hW hrect
    simpa only [hcard,Nat.cast_add,Nat.cast_one] using h
  have hRD : R ≤ D*n := by
    simpa only [R,a,map_sub,← dist_eq_norm] using walkSegment_dist_le z (by linarith) hz hs ht
  have hAupper : R*W ≤ D^2*(n:ℝ)^2 := by
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
    have hm := mul_le_mul hRD hRD (by linarith : 0 ≤ R) (by positivity : 0 ≤ D*n)
    have hw := mul_le_mul_of_nonneg_left hWR (by linarith : 0 ≤ R)
    linarith
  refine ⟨R,W,e,c,hW,hWR,he,hrect,by linarith,hAupper,?_⟩
  have hdif := card_le_card_differences (E := walkSegment z n)
    ⟨z 0,(mem_walkSegment _ _ _).mpr ⟨0,by omega,rfl⟩⟩
  have hcountdif : (n:ℝ)+1 ≤ ((differences (walkSegment z n)).card:ℝ) := by
    rw [hcard] at hdif
    exact_mod_cast hdif
  by_cases hthin : |(e*((z u:ℂ)-c)).im| ≤ 1
  · have hWeq : W = 1 := max_eq_left hthin
    rw [hWeq,mul_one]
    have hdn : D*(n:ℝ) ≤ D*((differences (walkSegment z n)).card:ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    exact (hRD.trans hdn).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hWeq : W = |(e*((z u:ℂ)-c)).im| := max_eq_right (by linarith)
    let b := z u-z t
    have hdet : |((a.re*b.im-a.im*b.re:ℤ):ℝ)| = R*W := by
      rw [diameter_height,hWeq]
      simp only [R,e,b,map_sub,c]
    have hab : a.re*b.im-a.im*b.re ≠ 0 := by
      intro hh
      rw [hh,Int.cast_zero,abs_zero] at hdet
      have : 0 < R*W := mul_pos (by linarith) (by linarith)
      linarith
    have hcd := differences_card_of_triangle z ht hs hu' (by linarith) hz hab
    have hcd' : |((a.re*b.im-a.im*b.re:ℤ):ℝ)| ≤
        ((differences (walkSegment z n)).card:ℝ)*((latticeBall (4*D)).card:ℝ) := by
      have hh : ((a.re*b.im-a.im*b.re).natAbs:ℝ) ≤
          ((differences (walkSegment z n)).card:ℝ)*((latticeBall (4*D)).card:ℝ) := by
        exact_mod_cast hcd
      simpa only [Nat.cast_natAbs,Int.cast_abs] using hh
    rw [hdet] at hcd'
    calc
      R*W ≤ ((differences (walkSegment z n)).card:ℝ)*((latticeBall (4*D)).card:ℝ) := hcd'
      _ = ((latticeBall (4*D)).card:ℝ)*((differences (walkSegment z n)).card:ℝ) := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat

namespace FinLaw

section

variable {Ω : Type uOmega} [Fintype Ω]

noncomputable def Hf {α : Type uAlpha} (p : FinLaw Ω) (X : Ω → α) : ℝ := by
  classical
  exact -∑ ω, p ω * Real.log (∑ ν, if X ν = X ω then p ν else 0)

noncomputable def cHf {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) : ℝ :=
  p.Hf (fun ω => (X ω,Y ω))-p.Hf Y

theorem Hf_eq_H {α : Type uAlpha} [Fintype α] (p : FinLaw Ω) (X : Ω → α) : p.Hf X = p.H X := by
  classical
  rw [H_eq_sum]
  simp only [Hf,map_mass]

theorem Hf_eq_of_fibers {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β)
    (hf : ∀ ω ν, X ω = X ν ↔ Y ω = Y ν) : p.Hf X = p.Hf Y := by
  classical
  unfold Hf
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  congr 2
  apply Finset.sum_congr rfl
  intro ν _
  rw [hf]

noncomputable def outputRange {α : Type uAlpha} (X : Ω → α) : Finset α := by
  classical
  exact Finset.univ.image X

noncomputable def outputCode {α : Type uAlpha} (X : Ω → α) (ω : Ω) : outputRange X :=
  ⟨X ω,by
    classical
    simp [outputRange]⟩

@[simp] theorem outputCode_eq_iff {α : Type uAlpha} (X : Ω → α) (ω ν : Ω) :
    outputCode X ω = outputCode X ν ↔ X ω = X ν := Subtype.ext_iff

theorem Hf_code {α : Type uAlpha} (p : FinLaw Ω) (X : Ω → α) :
    p.Hf X = p.H (outputCode X) := by
  rw [← Hf_eq_H]
  exact p.Hf_eq_of_fibers _ _ (fun _ _ => (outputCode_eq_iff _ _ _).symm)

theorem Hf_pair_code {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.Hf (fun ω => (X ω,Y ω)) = p.H (fun ω => (outputCode X ω,outputCode Y ω)) := by
  rw [← Hf_eq_H]
  apply p.Hf_eq_of_fibers
  simp only [Prod.mk.injEq,outputCode_eq_iff,implies_true]

theorem Hf_triple_code {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} (p : FinLaw Ω)
    (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.Hf (fun ω => (X ω,(Y ω,Z ω))) =
      p.H (fun ω => (outputCode X ω,(outputCode Y ω,outputCode Z ω))) := by
  rw [← Hf_eq_H]
  apply p.Hf_eq_of_fibers
  simp only [Prod.mk.injEq,outputCode_eq_iff,implies_true]

theorem Hf_nonneg {α : Type uAlpha} (p : FinLaw Ω) (X : Ω → α) : 0 ≤ p.Hf X := by
  rw [Hf_code]
  exact (p.map _).entropy_nonneg

theorem Hf_le_log_card_sample {α : Type uAlpha} (p : FinLaw Ω) (X : Ω → α) :
    p.Hf X ≤ Real.log (Fintype.card Ω) := by
  rw [Hf_code]
  refine (p.map _).entropy_le_log_card.trans ?_
  have hsel := Fintype.card_le_of_surjective (outputCode X) (fun ⟨x,hx⟩ => by
    classical
    obtain ⟨ω,_,hω⟩ := Finset.mem_image.mp hx
    exact ⟨ω,Subtype.ext hω⟩)
  exact Real.log_le_log (by exact_mod_cast Fintype.card_pos_iff.mpr (p.map (outputCode X)).nonempty)
    (by exact_mod_cast hsel)

theorem Hf_pair_comm {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.Hf (fun ω => (X ω,Y ω)) = p.Hf (fun ω => (Y ω,X ω)) := by
  apply p.Hf_eq_of_fibers
  simp only [Prod.mk.injEq,and_comm,implies_true]

theorem Hf_pair_assoc {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.Hf (fun ω => (X ω,(Y ω,Z ω))) = p.Hf (fun ω => ((X ω,Y ω),Z ω)) := by
  apply p.Hf_eq_of_fibers
  simp only [Prod.mk.injEq,and_assoc,implies_true]

theorem Hf_pair_ge_snd {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.Hf Y ≤ p.Hf (fun ω => (X ω,Y ω)) := by
  rw [Hf_pair_code,Hf_code]
  exact p.H_pair_ge_snd _ _

theorem Hf_pair_subadd {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.Hf (fun ω => (X ω,Y ω)) ≤ p.Hf X+p.Hf Y := by
  rw [Hf_pair_code,Hf_code p X,Hf_code p Y]
  exact p.H_pair_subadd _ _

theorem Hf_strong_subadd {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.Hf (fun ω => (X ω,(Y ω,Z ω)))+p.Hf Y ≤
      p.Hf (fun ω => (X ω,Y ω))+p.Hf (fun ω => (Y ω,Z ω)) := by
  rw [Hf_triple_code,Hf_code p Y,Hf_pair_code p X Y,Hf_pair_code p Y Z]
  exact p.H_strong_subadd _ _ _

theorem cHf_nonneg {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    0 ≤ p.cHf X Y := sub_nonneg.mpr (p.Hf_pair_ge_snd X Y)

theorem cHf_le_Hf {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.cHf X Y ≤ p.Hf X := by have := p.Hf_pair_subadd X Y; unfold cHf; linarith

theorem cHf_mono {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.cHf X (fun ω => (Y ω,Z ω)) ≤ p.cHf X Y := by
  have := p.Hf_strong_subadd X Y Z
  unfold cHf
  linarith

theorem Hf_comp_le {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (f : α → β) :
    p.Hf (f ∘ X) ≤ p.Hf X := by
  have h := p.Hf_pair_ge_snd X (f ∘ X)
  have he : p.Hf (fun ω => (X ω,(f ∘ X) ω)) = p.Hf X :=
    p.Hf_eq_of_fibers _ _ (fun _ _ => by
      simp only [Prod.mk.injEq,Function.comp_def]
      exact ⟨And.left,fun hh => ⟨hh,congrArg f hh⟩⟩)
  rwa [he] at h

theorem Hf_le_of_determined {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β)
    (h : ∀ ω ν, Y ω = Y ν → X ω = X ν) : p.Hf X ≤ p.Hf Y := by
  have hh := p.Hf_pair_ge_snd Y X
  have he : p.Hf (fun ω => (Y ω,X ω)) = p.Hf Y :=
    p.Hf_eq_of_fibers _ _ (fun ω ν => by
      simp only [Prod.mk.injEq]
      exact ⟨And.left,fun hh => ⟨hh,h ω ν hh⟩⟩)
  rwa [he] at hh

theorem Hf_const {α : Type uAlpha} (p : FinLaw Ω) (a : α) : p.Hf (fun _ => a) = 0 := by
  classical
  simp [Hf,p.sum_one]

theorem Hf_finset_subadd {ι : Type uIota} {α : Type uAlpha} (p : FinLaw Ω) (X : Ω → ι → α) (S : Finset ι) :
    p.Hf (fun ω (i : S) => X ω i) ≤ ∑ i ∈ S, p.Hf (fun ω => X ω i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have he : p.Hf (fun ω (i : (∅:Finset ι)) => X ω i) = p.Hf (fun _ => ()) := by
      apply p.Hf_eq_of_fibers
      intro ω ν
      simp only [iff_true]
      funext i
      exact False.elim (Finset.notMem_empty i.val i.property)
    simp [he,p.Hf_const]
  | @insert i S hi ih =>
    have he : p.Hf (fun ω (j : (insert i S : Finset ι)) => X ω j) =
        p.Hf (fun ω => (X ω i,fun j : S => X ω j)) := by
      apply p.Hf_eq_of_fibers
      intro ω ν
      constructor
      · intro h
        apply Prod.ext
        · exact congrFun h ⟨i,Finset.mem_insert_self _ _⟩
        · funext j; exact congrFun h ⟨j,Finset.mem_insert_of_mem j.property⟩
      · intro h
        funext j
        rcases Finset.mem_insert.mp j.property with hj | hj
        · simpa [hj] using congrArg Prod.fst h
        · exact congrFun (congrArg Prod.snd h) ⟨j,hj⟩
    rw [he,Finset.sum_insert hi]
    have hh := p.Hf_pair_subadd (fun ω => X ω i) (fun ω (j : S) => X ω j)
    linarith

end
open scoped BigOperators

variable {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω] {k : ℕ}

def prefixVar (X : Ω → Fin k → α) (π : Equiv.Perm (Fin k)) (s : ℕ) (ω : Ω) (i : Fin k) : Option α :=
  if i.val < s then some (X ω (π i)) else none

noncomputable def orderedEntropy (p : FinLaw Ω) (X : Ω → Fin k → α) (s : ℕ) : ℝ :=
  𝔼 π : Equiv.Perm (Fin k), p.Hf (prefixVar X π s)

omit [Fintype Ω] in
@[simp] theorem prefixVar_zero (X : Ω → Fin k → α) (π : Equiv.Perm (Fin k)) (ω : Ω) :
    prefixVar X π 0 ω = fun _ => none := by funext i; simp [prefixVar]

@[simp] theorem orderedEntropy_zero (p : FinLaw Ω) (X : Ω → Fin k → α) :
    p.orderedEntropy X 0 = 0 := by
  have h (π : Equiv.Perm (Fin k)) : prefixVar X π 0 = fun _ _ => none := by
    funext ω i
    simp [prefixVar]
  simp [orderedEntropy,h,Finset.expect,p.Hf_const]

theorem orderedEntropy_nonneg (p : FinLaw Ω) (X : Ω → Fin k → α) (s : ℕ) :
    0 ≤ p.orderedEntropy X s := Finset.expect_nonneg (fun _ _ => p.Hf_nonneg _)

theorem prefixVar_chain (p : FinLaw Ω) (X : Ω → Fin k → α) (π : Equiv.Perm (Fin k))
    {s : ℕ} (hs : s < k) :
    p.Hf (prefixVar X π (s+1)) =
      p.Hf (fun ω => (X ω (π ⟨s,hs⟩),prefixVar X π s ω)) := by
  apply p.Hf_eq_of_fibers
  intro ω ν
  constructor
  · intro h
    apply Prod.ext
    · have hh := congrFun h ⟨s,hs⟩
      simpa [prefixVar] using hh
    · funext i
      by_cases hi : i.val < s
      · have hh := congrFun h i
        simpa [prefixVar,hi,show i.val<s+1 by omega] using hh
      · simp [prefixVar,hi]
  · intro h
    funext i
    by_cases hi : i.val < s
    · have hh := congrFun (congrArg Prod.snd h) i
      simpa [prefixVar,hi,show i.val<s+1 by omega] using hh
    · by_cases his : i.val = s
      · have hieq : i = ⟨s,hs⟩ := Fin.ext his
        subst i
        simpa [prefixVar] using congrArg some (congrArg Prod.fst h)
      · simp [prefixVar,show ¬i.val<s+1 by omega]

theorem orderedEntropy_step (p : FinLaw Ω) (X : Ω → Fin k → α) {s : ℕ} (hs : s < k) :
    p.orderedEntropy X (s+1)-p.orderedEntropy X s =
      𝔼 π : Equiv.Perm (Fin k), p.cHf (fun ω => X ω (π ⟨s,hs⟩)) (prefixVar X π s) := by
  simp only [orderedEntropy,← Finset.expect_sub_distrib,cHf,p.prefixVar_chain X _ hs]

theorem ordered_remaining_exchange (p : FinLaw Ω) (X : Ω → Fin k → α) (s : ℕ)
    (i j : Fin k) (hi : s ≤ i.val) (hj : s ≤ j.val) :
    (𝔼 π : Equiv.Perm (Fin k), p.cHf (fun ω => X ω (π i)) (prefixVar X π s)) =
      𝔼 π : Equiv.Perm (Fin k), p.cHf (fun ω => X ω (π j)) (prefixVar X π s) := by
  classical
  apply Fintype.expect_equiv (Equiv.mulRight (Equiv.swap i j))
  intro π
  have hp : prefixVar X (π*Equiv.swap i j) s = prefixVar X π s := by
    funext ω a
    by_cases ha : a.val<s
    · have hai : a≠i := by intro he; subst a; omega
      have haj : a≠j := by intro he; subst a; omega
      simp [prefixVar,ha,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hai haj]
    · simp [prefixVar,ha]
  change p.cHf (fun ω => X ω (π i)) (prefixVar X π s) =
    p.cHf (fun ω => X ω ((π * Equiv.swap i j) j)) (prefixVar X (π * Equiv.swap i j) s)
  rw [hp]
  simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_right]

theorem cHf_mono_of_refines {β : Type uBeta} {γ : Type uGamma} (p : FinLaw Ω)
    (X : Ω → α) (Y : Ω → β) (Z : Ω → γ)
    (h : ∀ ω ν, Y ω = Y ν → Z ω = Z ν) : p.cHf X Y ≤ p.cHf X Z := by
  have hc := p.cHf_mono X Z Y
  have hy : p.Hf (fun ω => (Z ω,Y ω)) = p.Hf Y := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    simp only [Prod.mk.injEq]
    exact ⟨And.right,fun hh => ⟨h ω ν hh,hh⟩⟩
  have hx : p.Hf (fun ω => (X ω,(Z ω,Y ω))) = p.Hf (fun ω => (X ω,Y ω)) := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    simp only [Prod.mk.injEq]
    exact ⟨fun hh => ⟨hh.1,hh.2.2⟩,fun hh => ⟨hh.1,h ω ν hh.2,hh.2⟩⟩
  unfold cHf at hc ⊢
  rwa [hy,hx] at hc

theorem orderedEntropy_concave (p : FinLaw Ω) (X : Ω → Fin k → α) {s : ℕ} (hs : s+1 < k) :
    p.orderedEntropy X (s+2)-p.orderedEntropy X (s+1) ≤
      p.orderedEntropy X (s+1)-p.orderedEntropy X s := by
  rw [p.orderedEntropy_step X hs,p.orderedEntropy_step X (by omega : s<k)]
  rw [p.ordered_remaining_exchange X s ⟨s,by omega⟩ ⟨s+1,hs⟩ (by exact le_rfl) (by exact Nat.le_succ s)]
  apply Finset.expect_le_expect
  intro π _
  apply p.cHf_mono_of_refines
  intro ω ν hh
  funext a
  by_cases ha : a.val < s
  · simpa [prefixVar,ha,show a.val < s+1 by omega] using congrFun hh a
  · simp [prefixVar,ha]

theorem orderedEntropy_slope (p : FinLaw Ω) (X : Ω → Fin k → α)
    {b : ℕ} (hb : 0 < b) (hbk : b < k) :
    p.orderedEntropy X (b+1)-p.orderedEntropy X b ≤ p.orderedEntropy X b / b := by
  have h (s : ℕ) (hs : s < k) :
      (s : ℝ)*(p.orderedEntropy X (s+1)-p.orderedEntropy X s) ≤ p.orderedEntropy X s := by
    induction s with
    | zero => simp
    | succ s ih =>
      have ih' := ih (by omega)
      have hc := p.orderedEntropy_concave X hs
      have hn : (0 : ℝ) ≤ s+1 := by positivity
      have hm := mul_le_mul_of_nonneg_left hc hn
      simp only [Nat.cast_add,Nat.cast_one] at *
      linarith
  exact (le_div_iff₀ (by exact_mod_cast hb)).mpr (by linarith [h b hbk])

noncomputable def signedEntropy (p : FinLaw Ω) (X : (Fin k → Bool) → Ω → Fin k → α) (s : ℕ) : ℝ :=
  𝔼 σ : Fin k → Bool, p.orderedEntropy (X σ) s

@[simp] theorem signedEntropy_zero (p : FinLaw Ω) (X : (Fin k → Bool) → Ω → Fin k → α) :
    p.signedEntropy X 0 = 0 := by simp [signedEntropy,Finset.expect]

theorem signedEntropy_slope (p : FinLaw Ω) (X : (Fin k → Bool) → Ω → Fin k → α)
    {b : ℕ} (hb : 0 < b) (hbk : b < k) :
    p.signedEntropy X (b+1)-p.signedEntropy X b ≤ p.signedEntropy X b / b := by
  unfold signedEntropy
  rw [← Finset.expect_sub_distrib,Finset.expect_div]
  exact Finset.expect_le_expect (fun σ _ => p.orderedEntropy_slope (X σ) hb hbk)

theorem cHf_chain {β : Type uBeta} {γ : Type uGamma} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.cHf (fun ω => (X ω,Y ω)) Z = p.cHf X Z + p.cHf Y (fun ω => (X ω,Z ω)) := by
  unfold cHf
  have he : p.Hf (fun ω => ((X ω,Y ω),Z ω)) = p.Hf (fun ω => (Y ω,(X ω,Z ω))) := by
    apply p.Hf_eq_of_fibers
    simp only [Prod.mk.injEq]
    tauto
  rw [he]
  ring

theorem cHf_pair_subadd {β : Type uBeta} {γ : Type uGamma} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.cHf (fun ω => (X ω,Y ω)) Z ≤ p.cHf X Z + p.cHf Y Z := by
  rw [p.cHf_chain]
  apply add_le_add le_rfl
  apply p.cHf_mono_of_refines
  intro ω ν h
  exact congrArg Prod.snd h

theorem enrichment_chain {β : Type uBeta} {γ : Type uGamma} {δ : Type uDelta} {ε : Type uEpsilon} {ζ : Type uZeta} (p : FinLaw Ω)
    (X : Ω → α) (Y : Ω → β) (Bx : Ω → γ) (By : Ω → δ) (h : Ω → ε) (H : Ω → ζ)
    (hh : ∀ ω ν, X ω = X ν → Y ω = Y ν → h ω = h ν)
    (hY : ∀ ω ν, X ω = X ν → h ω = h ν → Y ω = Y ν)
    (hH : ∀ ω ν, H ω = H ν → h ω = h ν) :
    p.cHf h (fun ω => (Bx ω,By ω)) ≤ p.cHf X Bx + p.cHf Y By -
      p.cHf X (fun ω => ((Bx ω,By ω),H ω)) := by
  let B := fun ω => (Bx ω,By ω)
  have he : p.cHf (fun ω => (h ω,X ω)) B = p.cHf (fun ω => (X ω,Y ω)) B := by
    unfold cHf
    congr 1
    apply p.Hf_eq_of_fibers
    intro ω ν
    simp only [Prod.mk.injEq]
    exact ⟨fun ha => ⟨⟨ha.1.2,hY ω ν ha.1.2 ha.1.1⟩,ha.2⟩,
      fun ha => ⟨⟨hh ω ν ha.1.1 ha.1.2,ha.1.1⟩,ha.2⟩⟩
  have hx : p.cHf X B ≤ p.cHf X Bx :=
    p.cHf_mono_of_refines _ _ _ (fun _ _ he => congrArg Prod.fst he)
  have hy : p.cHf Y B ≤ p.cHf Y By :=
    p.cHf_mono_of_refines _ _ _ (fun _ _ he => congrArg Prod.snd he)
  have ht : p.cHf X (fun ω => (B ω,H ω)) ≤ p.cHf X (fun ω => (h ω,B ω)) := by
    apply p.cHf_mono_of_refines
    intro ω ν he
    apply Prod.ext
    · exact hH ω ν (congrArg Prod.snd he)
    · exact congrArg Prod.fst he
  have hc := p.cHf_chain h X B
  have hs := p.cHf_pair_subadd X Y B
  change p.cHf h B ≤ p.cHf X Bx + p.cHf Y By - p.cHf X (fun ω => (B ω,H ω))
  linarith

end FinLaw

end GaussianMoat

end OAI
end
end

section
section
namespace OAI

namespace GaussianMoat

noncomputable def multiples (π : GaussianInt) : Submodule ℤ GaussianInt :=
  (twoVectorMap π (π * ⟨0,1⟩)).range

lemma twoVectorMap_mul_i (π z : GaussianInt) :
    twoVectorMap π (π * ⟨0,1⟩) z = π*z := by
  rw [twoVectorMap_apply]
  ext <;> simp [zsmul_eq_mul,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> ring

lemma mem_multiples (π z : GaussianInt) : z ∈ multiples π ↔ π ∣ z := by
  simp only [multiples, LinearMap.mem_range, twoVectorMap_mul_i]
  exact ⟨fun ⟨a,ha⟩ => ⟨a,ha.symm⟩,fun ⟨a,ha⟩ => ⟨a,ha.symm⟩⟩

lemma multiples_index {π : GaussianInt} (hπ : π ≠ 0) :
    Nat.card (GaussianInt ⧸ multiples π) = π.norm.natAbs := by
  have he : π.re*(π*⟨0,1⟩).im-π.im*(π*⟨0,1⟩).re = π.norm := by
    simp [Zsqrtd.re_mul,Zsqrtd.im_mul,Zsqrtd.norm]
  have hn : π.norm ≠ 0 := (GaussianInt.norm_pos.mpr hπ).ne'
  have h := twoVectorMap_quotient_card (a := π) (b := π*⟨0,1⟩) (he.trans_ne hn)
  simpa only [multiples,he] using h

noncomputable def gaussianResidue (π z : GaussianInt) : GaussianInt ⧸ multiples π :=
  Submodule.Quotient.mk z

lemma gaussianResidue_eq (π z w : GaussianInt) :
    gaussianResidue π z = gaussianResidue π w ↔ π ∣ z-w := by
  rw [gaussianResidue,gaussianResidue,Submodule.Quotient.eq,mem_multiples]

instance : Countable GaussianInt := latticeCoords.injective.countable

instance (π : GaussianInt) : Countable (GaussianInt ⧸ multiples π) :=
  (Submodule.Quotient.mk_surjective (p := multiples π)).countable

noncomputable def residueCode (π z : GaussianInt) : ℕ := by
  let := Encodable.ofCountable (GaussianInt ⧸ multiples π)
  exact Encodable.encode (gaussianResidue π z)

lemma residueCode_eq (π z w : GaussianInt) :
    residueCode π z = residueCode π w ↔ π ∣ z-w := by
  let := Encodable.ofCountable (GaussianInt ⧸ multiples π)
  change Encodable.encode (gaussianResidue π z) = Encodable.encode (gaussianResidue π w) ↔ _
  rw [Encodable.encode_inj,gaussianResidue_eq]

lemma residueCode_sub {π x y x' y' : GaussianInt}
    (hx : residueCode π x = residueCode π x') (hy : residueCode π y = residueCode π y') :
    residueCode π (x-y) = residueCode π (x'-y') := by
  rw [residueCode_eq] at *
  convert dvd_sub hx hy using 1; ring

lemma residueCode_add {π x y x' y' : GaussianInt}
    (hx : residueCode π x = residueCode π x') (hy : residueCode π y = residueCode π y') :
    residueCode π (x+y) = residueCode π (x'+y') := by
  rw [residueCode_eq] at *
  convert dvd_add hx hy using 1; ring

lemma finite_gaussianResidue {π : GaussianInt} (hπ : π ≠ 0) :
    Finite (GaussianInt ⧸ multiples π) := by
  apply Nat.finite_of_card_ne_zero
  rw [multiples_index hπ]
  simpa only [Int.natAbs_ne_zero] using (GaussianInt.norm_pos.mpr hπ).ne'

lemma residueCode_range_card {π : GaussianInt} (hπ : π ≠ 0) :
    (Set.range (residueCode π)).Finite ∧ (Set.range (residueCode π)).ncard = π.norm.natAbs := by
  let := finite_gaussianResidue hπ
  let := Encodable.ofCountable (GaussianInt ⧸ multiples π)
  have hs : Function.Surjective (gaussianResidue π) := Submodule.Quotient.mk_surjective _
  have hr : Set.range (residueCode π) = Set.range
      (Encodable.encode : (GaussianInt ⧸ multiples π) → ℕ) := by
    change Set.range (Encodable.encode ∘ gaussianResidue π) = _
    rw [Set.range_comp,hs.range_eq,Set.image_univ]
  rw [hr]
  refine ⟨Set.finite_range _,?_⟩
  rw [Set.ncard_range_of_injective Encodable.encode_injective,multiples_index hπ]

end GaussianMoat

end OAI
end
end

section
section
namespace OAI

namespace GaussianMoat

open Filter Topology Finset
namespace PrimeLogMass
open ArithmeticFunction.vonMangoldt Complex

lemma residue_real_series {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    {x : ℝ} (hx : 1 < x) :
    ∑' n, residueClass a n / (n : ℝ) ^ x =
      (LFunctionResidueClassAux a x).re + (q.totient : ℝ)⁻¹ / (x - 1) := by
  refine ofReal_injective ?_
  simp only [ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast,
    ofReal_add, ofReal_inv, ofReal_sub, ofReal_one]
  simp_rw [← LFunctionResidueClassAux_real ha hx,
    eqOn_LFunctionResidueClassAux ha <| Set.mem_ofPred.mpr (ofReal_re x ▸ hx), sub_add_cancel,
    LSeries, LSeries.term]
  refine tsum_congr fun n ↦ ?_
  split_ifs with hn
  · simp only [hn, residueClass_apply_zero, ofReal_zero, zero_div]
  · rfl

theorem residue_moment_limit {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    {j : ℝ} (hj : 0 < j) :
    Tendsto (fun X : ℝ => (∑' n, residueClass a n / (n : ℝ) ^ (1+j/X)) / X)
      atTop (𝓝 ((q.totient : ℝ)⁻¹ / j)) := by
  have hinv : Tendsto (fun X : ℝ => j/X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have harg : Tendsto (fun X : ℝ => ((1+j/X : ℝ) : ℂ)) atTop (𝓝 1) := by
    have hr : Tendsto (fun X : ℝ => 1+j/X) atTop (𝓝 1) := by
      simpa using hinv.const_add 1
    simpa only [Function.comp_def,ofReal_one] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  have hmem : ∀ᶠ X : ℝ in atTop, ((1+j/X : ℝ) : ℂ) ∈ {s : ℂ | 1 ≤ s.re} := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    change 1 ≤ 1+j/X
    exact le_add_of_nonneg_right (div_nonneg hj.le hX.le)
  have hc : Tendsto (fun X : ℝ => (LFunctionResidueClassAux a ((1+j/X : ℝ) : ℂ)).re)
      atTop (𝓝 (LFunctionResidueClassAux a 1).re) := by
    exact Complex.continuous_re.continuousAt.tendsto.comp
      ((continuousOn_LFunctionResidueClassAux a 1 (by simp)).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨harg,hmem⟩))
  have hz := hc.div_atTop tendsto_id
  have hl : Tendsto (fun X : ℝ => (LFunctionResidueClassAux a ((1+j/X : ℝ) : ℂ)).re / X +
      (q.totient : ℝ)⁻¹ / j) atTop (𝓝 ((q.totient : ℝ)⁻¹ / j)) := by
    simpa using hz.add_const ((q.totient : ℝ)⁻¹ / j)
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  rw [residue_real_series ha (by linarith [div_pos hj hX] : 1 < 1+j/X)]
  rw [add_div,add_sub_cancel_left,div_div,div_mul_cancel₀ _ hX.ne']

open intervalIntegral MeasureTheory

noncomputable def betaMoment (m n : ℕ) : ℝ := ∫ x in (0 : ℝ)..1, x^m*(1-x)^n

lemma betaMoment_pos (m n : ℕ) : 0 < betaMoment m n := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (by fun_prop : Continuous (fun x : ℝ => x^m*(1-x)^n)).intervalIntegrable _ _
  · intro x hx
    exact mul_pos (pow_pos hx.1 _) (pow_pos (sub_pos.mpr hx.2) _)
  · norm_num

lemma betaMoment_succ (m n : ℕ) :
    betaMoment (m+1) n = (m+1 : ℝ)/(m+n+2)*betaMoment m n := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => x^(m+1)*(1-x)^(n+1))
      ((m+1 : ℝ)*x^m*(1-x)^(n+1) - (n+1 : ℝ)*x^(m+1)*(1-x)^n) x := by
    have h1 : HasDerivAt (fun y : ℝ => y^(m+1)) ((m+1 : ℝ)*x^m) x := by
      simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using hasDerivAt_pow (m+1) x
    have h2 : HasDerivAt (fun y : ℝ => (1-y)^(n+1)) (-(n+1 : ℝ)*(1-x)^n) x := by
      simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, id_eq, sub_zero, zero_sub,
        mul_neg_one, neg_mul] using! ((hasDerivAt_id x).const_sub 1).pow (n+1)
    convert! h1.mul h2 using 1; ring
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (by exact (by fun_prop : Continuous (fun x : ℝ =>
      (m+1 : ℝ)*x^m*(1-x)^(n+1)-(n+1 : ℝ)*x^(m+1)*(1-x)^n)).intervalIntegrable 0 1)
  have hsplit : betaMoment m (n+1)+betaMoment (m+1) n = betaMoment m n := by
    unfold betaMoment
    rw [← intervalIntegral.integral_add]
    · congr 1
      funext x
      rw [pow_succ,pow_succ]
      ring
    · exact (by fun_prop : Continuous (fun x : ℝ => x^m*(1-x)^(n+1))).intervalIntegrable _ _
    · exact (by fun_prop : Continuous (fun x : ℝ => x^(m+1)*(1-x)^n)).intervalIntegrable _ _
  have hi (u v : ℕ) : IntervalIntegrable (fun x : ℝ => x^u*(1-x)^v) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have hmul (c : ℝ) (u v : ℕ) :
      (∫ x : ℝ in 0..1, c*x^u*(1-x)^v) = c*betaMoment u v := by
    simp only [mul_assoc,intervalIntegral.integral_const_mul,betaMoment]
  rw [intervalIntegral.integral_sub
    (by simpa only [mul_assoc] using (hi m (n+1)).const_mul (m+1 : ℝ))
    (by simpa only [mul_assoc] using (hi (m+1) n).const_mul (n+1 : ℝ)),
    hmul,hmul] at hInt
  simp only [one_pow,sub_self,zero_pow (Nat.succ_ne_zero _),mul_zero,zero_mul,sub_zero] at hInt
  have hn : (0 : ℝ) < m+n+2 := by positivity
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hn.ne').mpr
  nlinarith

noncomputable def windowPolynomialAux (m n : ℕ) : Polynomial ℝ :=
  Polynomial.X^m*(1-Polynomial.X)^n*
    ((Polynomial.X-Polynomial.C (7/20))*(Polynomial.C (11/30)-Polynomial.X))

lemma windowPolynomialAux_eval (m n : ℕ) (y : ℝ) :
    Polynomial.eval y (windowPolynomialAux m n) = y^m*(1-y)^n*((y-7/20)*(11/30-y)) := by
  simp only [windowPolynomialAux,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_X,Polynomial.eval_C]

noncomputable def windowPolynomial : Polynomial ℝ := windowPolynomialAux 1431 2567

lemma windowPolynomial_eval (y : ℝ) :
    Polynomial.eval y windowPolynomial = y^1431*(1-y)^2567*((y-7/20)*(11/30-y)) :=
  windowPolynomialAux_eval 1431 2567 y

lemma windowPolynomial_nonpos {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hout : y ≤ 7/20 ∨ 11/30 ≤ y) : Polynomial.eval y windowPolynomial ≤ 0 := by
  rw [windowPolynomial_eval]
  have hp : 0 ≤ y^1431*(1-y)^2567 := mul_nonneg (pow_nonneg hy.1 _) (pow_nonneg (sub_nonneg.mpr hy.2) _)
  apply mul_nonpos_of_nonneg_of_nonpos hp
  rcases hout with hl | hr
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hl]) (by linarith only [hl])
  · exact mul_nonpos_of_nonneg_of_nonpos (by linarith only [hr]) (by linarith only [hr])

lemma betaMoment_quadratic (m n : ℕ) (a b : ℝ) :
    (∫ x : ℝ in 0..1, x^m*(1-x)^n*((x-a)*(b-x))) =
      (a+b)*betaMoment (m+1) n-betaMoment (m+2) n-a*b*betaMoment m n := by
  have he : (fun x : ℝ => x^m*(1-x)^n*((x-a)*(b-x))) = fun x =>
      (a+b)*(x^(m+1)*(1-x)^n)-(x^(m+2)*(1-x)^n)-a*b*(x^m*(1-x)^n) := by
    funext x
    simp only [pow_add,pow_one,pow_two]
    ring
  have hi (u v : ℕ) : IntervalIntegrable (fun x : ℝ => x^u*(1-x)^v) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [he,intervalIntegral.integral_sub ((hi (m+1) n).const_mul _ |>.sub (hi (m+2) n))
    ((hi m n).const_mul _),
    intervalIntegral.integral_sub ((hi (m+1) n).const_mul _) (hi (m+2) n),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  rfl

lemma windowPolynomial_integral_pos : 0 < ∫ x : ℝ in 0..1, Polynomial.eval x windowPolynomial := by
  simp only [windowPolynomial_eval]
  rw [betaMoment_quadratic]
  change 0 < (7/20+11/30)*betaMoment 1432 2567 - betaMoment 1433 2567 -
    (7/20*(11/30))*betaMoment 1431 2567
  rw [betaMoment_succ 1432 2567, betaMoment_succ 1431 2567]
  norm_num only [Nat.cast_ofNat]
  have hp := betaMoment_pos 1431 2567
  linarith

lemma polynomial_integral_coeff (P : Polynomial ℝ) :
    (∫ x : ℝ in 0..1, P.eval x) = ∑ j ∈ P.support, P.coeff j / (j+1 : ℝ) := by
  simp_rw [Polynomial.eval_eq_sum,Polynomial.sum_def]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul,integral_pow,one_pow,
      zero_pow (Nat.succ_ne_zero _),sub_zero,mul_one_div]
  · intro j _
    exact (by fun_prop : Continuous (fun x : ℝ => P.coeff j*x^j)).intervalIntegrable _ _

theorem residue_polynomial_moment_limit {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    (P : Polynomial ℝ) :
    Tendsto (fun X : ℝ => ∑ j ∈ P.support, P.coeff j *
      ((∑' n, residueClass a n / (n : ℝ) ^ (1+(j+1 : ℝ)/X)) / X)) atTop
      (𝓝 ((q.totient : ℝ)⁻¹ * (∫ x : ℝ in 0..1, P.eval x))) := by
  have h (j : ℕ) := (residue_moment_limit ha (show (0 : ℝ) < j+1 by positivity)).const_mul (P.coeff j)
  have hs := tendsto_finsetSum P.support (fun j _ => h j)
  convert hs using 1
  congr 1
  rw [polynomial_integral_coeff,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma residue_summable {q : ℕ} [NeZero q] (a : ZMod q) {x : ℝ} (hx : 1 < x) :
    Summable (fun n : ℕ => residueClass a n / (n : ℝ)^x) :=
  LSeries.summable_real_of_abscissaOfAbsConv_lt
    ((abscissaOfAbsConv_residueClass_le_one a).trans_lt (by exact_mod_cast hx))

lemma laplace_power (n j : ℕ) (X : ℝ) (hn : n ≠ 0) :
    (n : ℝ) ^ (-(j+1 : ℝ)/X) =
      (Real.exp (-Real.log n / X))^(j+1) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn), ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma laplace_term {q : ℕ} [NeZero q] (a : ZMod q) (n j : ℕ) (X : ℝ) :
    residueClass a n / (n : ℝ)^(1+(j+1 : ℝ)/X) =
      residueClass a n / n * (Real.exp (-Real.log n/X))^(j+1) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · rw [Real.rpow_add (by exact_mod_cast hn),Real.rpow_one,div_mul_eq_div_div,
      div_eq_mul_inv _ ((n : ℝ)^((j+1 : ℝ)/X)), ← Real.rpow_neg (by positivity),
      show -((j+1 : ℝ)/X) = -(j+1 : ℝ)/X by ring,laplace_power n j X (by omega)]

lemma polynomial_laplace_series {q : ℕ} [NeZero q] (a : ZMod q)
    (P : Polynomial ℝ) {X : ℝ} (hX : 0 < X) :
    (∑ j ∈ P.support, P.coeff j *
      (∑' n, residueClass a n / (n : ℝ)^(1+(j+1 : ℝ)/X))) =
    ∑' n, residueClass a n / n * Real.exp (-Real.log n/X) *
      Polynomial.eval (Real.exp (-Real.log n/X)) P := by
  have hs (j : ℕ) : Summable (fun n : ℕ => residueClass a n /
      (n : ℝ)^(1+(j+1 : ℝ)/X)) := residue_summable a (by
    have : 0 < (j+1 : ℝ)/X := div_pos (by positivity) hX
    linarith)
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun j _ => (hs j).mul_left (P.coeff j))]
  apply tsum_congr
  intro n
  simp_rw [laplace_term,Polynomial.eval_eq_sum,Polynomial.sum_def,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ]
  ring

lemma polynomial_laplace_summable {q : ℕ} [NeZero q] (a : ZMod q)
    (P : Polynomial ℝ) {X : ℝ} (hX : 0 < X) :
    Summable (fun n : ℕ => residueClass a n / n * Real.exp (-Real.log n/X) *
      Polynomial.eval (Real.exp (-Real.log n/X)) P) := by
  have hs (j : ℕ) : Summable (fun n : ℕ => P.coeff j * (residueClass a n /
      (n : ℝ)^(1+(j+1 : ℝ)/X))) := (residue_summable a (by
    have : 0 < (j+1 : ℝ)/X := div_pos (by positivity) hX
    linarith)).mul_left _
  apply (summable_sum (s := P.support) (fun j _ => hs j)).congr
  intro n
  simp_rw [laplace_term,Polynomial.eval_eq_sum,Polynomial.sum_def,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ]
  ring

lemma windowPolynomial_le_one {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    Polynomial.eval y windowPolynomial ≤ 1 := by
  by_cases hl : y ≤ 7/20
  · exact (windowPolynomial_nonpos hy (.inl hl)).trans (by norm_num)
  by_cases hr : 11/30 ≤ y
  · exact (windowPolynomial_nonpos hy (.inr hr)).trans (by norm_num)
  rw [windowPolynomial_eval]
  have h1 : 0 ≤ y^1431 := pow_nonneg hy.1 _
  have h2 : 0 ≤ (1-y)^2567 := pow_nonneg (by linarith only [hy.2]) _
  have he : y^1431*(1-y)^2567 ≤ 1 :=
    (mul_le_of_le_one_left h2 (pow_le_one₀ hy.1 hy.2)).trans
      (pow_le_one₀ (by linarith only [hy.2]) (by linarith only [hy.1]))
  have hf : (y-7/20)*(11/30-y) ≤ 1 :=
    (mul_le_of_le_one_left (by linarith only [hr]) (by linarith only [hy.2])).trans
      (by linarith only [hy.1])
  exact (mul_le_of_le_one_left
    (mul_nonneg (by linarith only [hl]) (by linarith only [hr])) he).trans hf

lemma exp_window_lower : Real.exp (-(10499/10000 : ℝ)) < 7/20 := by
  have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 499/10000)
  have he := Real.exp_one_gt_d9
  have hp : Real.exp (10499/10000 : ℝ) = Real.exp 1 * Real.exp (499/10000 : ℝ) := by
    rw [← Real.exp_add]
    norm_num
  rw [Real.exp_neg,hp]
  rw [inv_eq_one_div]
  apply (div_lt_iff₀ (by positivity)).mpr
  nlinarith

lemma exp_window_upper : (11/30 : ℝ) < Real.exp (-(1001/1000 : ℝ)) := by
  have h := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1/1000)
    (by norm_num : (1/1000 : ℝ) < 1)
  have hp : Real.exp (1001/1000 : ℝ) = Real.exp 1 * Real.exp (1/1000 : ℝ) := by
    rw [← Real.exp_add]
    norm_num
  rw [Real.exp_neg,inv_eq_one_div]
  apply (lt_div_iff₀ (Real.exp_pos _)).mpr
  rw [hp]
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos 1).le
  norm_num at hm
  linarith [Real.exp_one_lt_d9]

noncomputable def windowIndices (X : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊Real.exp (10499/10000*X)⌋₊+1)).filter (fun n => Real.exp (1001/1000*X) ≤ n)

lemma mem_windowIndices (X : ℝ) (n : ℕ) :
    n ∈ windowIndices X ↔ Real.exp (1001/1000*X) ≤ n ∧ (n : ℝ) ≤ Real.exp (10499/10000*X) := by
  simp only [windowIndices,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff,
    Nat.le_floor_iff (Real.exp_pos _).le,and_comm]

lemma laplace_window_nonpos {X : ℝ} (hX : 0 < X) (n : ℕ)
    (hn : n ≠ 0) (hout : n ∉ windowIndices X) :
    Polynomial.eval (Real.exp (-Real.log n/X)) windowPolynomial ≤ 0 := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  apply windowPolynomial_nonpos
  · exact ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) hX.le)⟩
  rw [mem_windowIndices,not_and_or] at hout
  rcases hout with hl | hr
  · right
    have : Real.log n < 1001/1000*X := (Real.log_lt_iff_lt_exp hnp).mpr (lt_of_not_ge hl)
    apply exp_window_upper.le.trans
    apply Real.exp_le_exp.mpr
    apply (le_div_iff₀ hX).mpr
    linarith
  · left
    have : 10499/10000*X < Real.log n := (Real.lt_log_iff_exp_lt hnp).mpr (lt_of_not_ge hr)
    apply le_trans _ exp_window_lower.le
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ hX).mpr
    linarith

lemma window_mass_dominates {q : ℕ} [NeZero q] (a : ZMod q) {X : ℝ} (hX : 0 < X) :
    (∑' n, residueClass a n / n * Real.exp (-Real.log n/X) *
      Polynomial.eval (Real.exp (-Real.log n/X)) windowPolynomial) ≤
      ∑ n ∈ windowIndices X, residueClass a n / n := by
  classical
  let f := fun n : ℕ => if n ∈ windowIndices X then residueClass a n / n else 0
  have hf : Summable f := summable_of_ne_finset_zero (s := windowIndices X) (by
    intro n hn
    simp [f,hn])
  have ht : (∑' n, f n) = ∑ n ∈ windowIndices X, residueClass a n / n := by
    rw [tsum_eq_sum (s := windowIndices X) (by intro n hn; simp [f,hn])]
    apply Finset.sum_congr rfl
    intro n hn
    simp [f,hn]
  rw [← ht]
  apply Summable.tsum_le_tsum _ (polynomial_laplace_summable a windowPolynomial hX) hf
  intro n
  by_cases hn : n = 0
  · subst n
    simp [f]
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  have hy : Real.exp (-Real.log n/X) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) hX.le)⟩
  have hw : 0 ≤ residueClass a n / n := div_nonneg (residueClass_nonneg a n) (Nat.cast_nonneg n)
  by_cases hm : n ∈ windowIndices X
  · simp only [f,ite_eq_left hm]
    calc
      _ ≤ residueClass a n / n * Real.exp (-Real.log n/X) := by
        exact mul_le_of_le_one_right (mul_nonneg hw hy.1) (windowPolynomial_le_one hy)
      _ ≤ _ := mul_le_of_le_one_right hw hy.2
  · simp only [f,ite_eq_right hm]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hw hy.1) (laplace_window_nonpos hX n hn hm)

theorem eventually_residue_window_mass {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
      c*X ≤ ∑ n ∈ windowIndices X, residueClass a n / n := by
  let c := (q.totient : ℝ)⁻¹ * (∫ x : ℝ in 0..1, Polynomial.eval x windowPolynomial)
  have hc : 0 < c := mul_pos (inv_pos.mpr (by exact_mod_cast q.totient.pos_of_neZero))
    windowPolynomial_integral_pos
  have hlim := residue_polynomial_moment_limit ha windowPolynomial
  have he : ∀ᶠ X : ℝ in atTop,
      c/2 < ∑ j ∈ windowPolynomial.support, windowPolynomial.coeff j *
        ((∑' n, residueClass a n / (n : ℝ)^(1+(j+1 : ℝ)/X)) / X) :=
    hlim.eventually (eventually_gt_nhds (by dsimp [c]; linarith only [hc] : c/2 < c))
  refine ⟨c/2,half_pos hc,?_⟩
  filter_upwards [he,eventually_gt_atTop (0 : ℝ)] with X h hX
  have hid := polynomial_laplace_series a windowPolynomial hX
  have h' : c/2 < (∑' n, residueClass a n / n * Real.exp (-Real.log n/X) *
      Polynomial.eval (Real.exp (-Real.log n/X)) windowPolynomial) / X := by
    rw [← hid,Finset.sum_div]
    simpa only [mul_div_assoc] using h
  exact ((lt_div_iff₀ hX).mp h').le.trans (window_mass_dominates a hX)

theorem eventually_prime_window_mass {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
      c*X ≤ ∑ n ∈ (windowIndices X).filter Nat.Prime, residueClass a n / n := by
  classical
  obtain ⟨c,hc,he⟩ := eventually_residue_window_mass ha
  let f : ℕ → ℝ := fun n => (if n.Prime then 0 else residueClass a n) / n
  have hf : Summable f := summable_residueClass_non_primes_div a
  have hn : ∀ n, 0 ≤ f n := by intro n; dsimp [f]; split_ifs <;> positivity [residueClass_nonneg a n]
  refine ⟨c/2,half_pos hc,?_⟩
  filter_upwards [he,eventually_ge_atTop (2*(∑' n, f n)/c)] with X hX hK
  have hb := hf.sum_le_tsum (windowIndices X) (fun n _ => hn n)
  have hid : (∑ n ∈ windowIndices X, residueClass a n/n) =
      (∑ n ∈ (windowIndices X).filter Nat.Prime, residueClass a n/n) +
      ∑ n ∈ windowIndices X, f n := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [f]
    split_ifs <;> simp
  rw [hid] at hX
  have hbig := (div_le_iff₀ hc).mp hK
  linarith

end PrimeLogMass

theorem irreducible_of_prime_norm {π : GaussianInt} {p : ℕ}
    (hp : p.Prime) (hn : π.norm = (p : ℤ)) : Irreducible π := by
  have hnp : π.norm.natAbs = p := by rw [hn]; simp
  constructor
  · intro hu
    have h := Zsqrtd.norm_eq_one_iff.mpr hu
    rw [hnp] at h
    exact hp.ne_one h
  · intro a b hab
    have he : a.norm.natAbs*b.norm.natAbs = p := by
      rw [← Int.natAbs_mul,← Zsqrtd.norm_mul,← hab,hnp]
    have hi : Irreducible p := (Nat.irreducible_iff_nat_prime p).mpr hp
    rcases hi.isUnit_or_isUnit he.symm with ha | hb
    · left
      apply Zsqrtd.norm_eq_one_iff.mp
      simpa only [Nat.isUnit_iff] using ha
    · right
      apply Zsqrtd.norm_eq_one_iff.mp
      simpa only [Nat.isUnit_iff] using hb

theorem exists_split_factor {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1) :
    ∃ π : GaussianInt, Irreducible π ∧ π.norm = (p : ℤ) := by
  let : Fact p.Prime := ⟨hp⟩
  have hnp : ¬ Irreducible (p : GaussianInt) := by
    intro hi
    have h := (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p).mp hi.prime
    omega
  obtain ⟨a,b,hab⟩ := GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible p hnp
  have hn : (⟨a,b⟩ : GaussianInt).norm = (p : ℤ) := by
    simp only [Zsqrtd.norm]
    norm_num only [Int.reduceNeg,neg_mul,sub_neg_eq_add]
    have h : (a : ℤ)^2+(b : ℤ)^2 = (p : ℤ) := by exact_mod_cast hab
    simpa only [pow_two,one_mul] using h
  exact ⟨⟨a,b⟩,irreducible_of_prime_norm hp hn,hn⟩

end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat
open Filter Topology Finset

namespace FinLaw
open scoped BigOperators
variable {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω] {k : ℕ}

theorem cHf_eq_of_fibers {β : Type uBeta} {γ : Type uGamma} (p : FinLaw Ω)
    (X : Ω → α) (Y : Ω → β) (C : Ω → γ)
    (h : ∀ ω ν, C ω = C ν → (X ω = X ν ↔ Y ω = Y ν)) :
    p.cHf X C = p.cHf Y C := by
  unfold cHf
  congr 1
  apply p.Hf_eq_of_fibers
  intro ω ν
  simp only [Prod.mk.injEq]
  constructor <;> intro hh
  · exact ⟨(h ω ν hh.2).mp hh.1,hh.2⟩
  · exact ⟨(h ω ν hh.2).mpr hh.1,hh.2⟩

theorem cHf_le_of_determined {β : Type uBeta} {γ : Type uGamma} (p : FinLaw Ω)
    (X : Ω → α) (Y : Ω → β) (C : Ω → γ)
    (h : ∀ ω ν, Y ω = Y ν → C ω = C ν → X ω = X ν) :
    p.cHf X C ≤ p.cHf Y C := by
  apply sub_le_sub_right
  apply p.Hf_le_of_determined
  intro ω ν hh
  rcases Prod.mk.inj hh with ⟨hy,hc⟩
  exact Prod.ext (h ω ν hy hc) hc

theorem cHf_finset_subadd {ι : Type uIota} {β : Type uBeta} (p : FinLaw Ω)
    (X : Ω → ι → α) (C : Ω → β) (S : Finset ι) :
    p.cHf (fun ω (i : S) => X ω i) C ≤ ∑ i ∈ S, p.cHf (fun ω => X ω i) C := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have he : p.cHf (fun ω (i : (∅:Finset ι)) => X ω i) C = p.cHf (fun _ => ()) C := by
      apply p.cHf_eq_of_fibers
      intro ω ν _
      simp only [iff_true]
      funext i
      exact False.elim (Finset.notMem_empty i.val i.property)
    have hc : p.cHf (fun _ => ()) C = 0 := by
      unfold cHf
      have hh := p.Hf_eq_of_fibers (fun ω => ((),C ω)) C (fun _ _ => by simp)
      rw [hh,sub_self]
    simp [he,hc]
  | @insert i S hi ih =>
    have he : p.cHf (fun ω (j : (insert i S : Finset ι)) => X ω j) C =
        p.cHf (fun ω => (X ω i,fun j : S => X ω j)) C := by
      apply p.cHf_eq_of_fibers
      intro ω ν _
      constructor
      · intro h
        apply Prod.ext
        · exact congrFun h ⟨i,Finset.mem_insert_self _ _⟩
        · funext j; exact congrFun h ⟨j,Finset.mem_insert_of_mem j.property⟩
      · intro h
        funext j
        rcases Finset.mem_insert.mp j.property with hj | hj
        · simpa [hj] using congrArg Prod.fst h
        · exact congrFun (congrArg Prod.snd h) ⟨j,hj⟩
    rw [he,Finset.sum_insert hi]
    have hh := p.cHf_pair_subadd (fun ω => X ω i) (fun ω (j : S) => X ω j) C
    linarith

theorem cHf_fintype_subadd {ι : Type uIota} {β : Type uBeta} [Fintype ι] (p : FinLaw Ω)
    (X : Ω → ι → α) (C : Ω → β) :
    p.cHf X C ≤ ∑ i, p.cHf (fun ω => X ω i) C := by
  have h := p.cHf_finset_subadd X C Finset.univ
  have he : p.cHf (fun ω (i : (Finset.univ : Finset ι)) => X ω i) C = p.cHf X C := by
    apply p.cHf_eq_of_fibers
    intro ω ν _
    exact ⟨fun hh => funext (fun i => congrFun hh ⟨i,Finset.mem_univ i⟩),
      fun hh => funext (fun i => congrFun hh i)⟩
  rwa [he] at h

omit [Fintype Ω] in

theorem prefixVar_swap (X : Ω → Fin k → α) (π : Equiv.Perm (Fin k)) (s : ℕ)
    (i j : Fin k) (hi : s ≤ i.val) (hj : s ≤ j.val) :
    prefixVar X (π*Equiv.swap i j) s = prefixVar X π s := by
  classical
  funext ω a
  by_cases ha : a.val<s
  · have hai : a≠i := by intro he; subst a; omega
    have haj : a≠j := by intro he; subst a; omega
    simp [prefixVar,ha,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hai haj]
  · simp [prefixVar,ha]

theorem ordered_remaining_exchange_cond {β : Type uBeta} (p : FinLaw Ω)
    (X : Ω → Fin k → α) (C : Equiv.Perm (Fin k) → Ω → β)
    (i j : Fin k) (hC : ∀ π, C (π*Equiv.swap i j) = C π) :
    (𝔼 π : Equiv.Perm (Fin k), p.cHf (fun ω => X ω (π i)) (C π)) =
      𝔼 π : Equiv.Perm (Fin k), p.cHf (fun ω => X ω (π j)) (C π) := by
  classical
  apply Fintype.expect_equiv (Equiv.mulRight (Equiv.swap i j))
  intro π
  change p.cHf (fun ω => X ω (π i)) (C π) =
    p.cHf (fun ω => X ω ((π*Equiv.swap i j) j)) (C (π*Equiv.swap i j))
  rw [hC]
  simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_right]

theorem prefix_conditional_block {β : Type uBeta} (p : FinLaw Ω)
    (X : Ω → Fin k → α) (π : Equiv.Perm (Fin k)) (C : Ω → β)
    {b q : ℕ} (hbq : b ≤ q) (hq : q ≤ k)
    (hC : ∀ ω ν, C ω = C ν → prefixVar X π b ω = prefixVar X π b ν) :
    p.cHf (prefixVar X π q) C ≤
      ∑ j : Fin (q-b), p.cHf (fun ω => X ω (π ⟨b+j.val,by omega⟩)) C := by
  let R := fun ω (j : Fin (q-b)) => X ω (π ⟨b+j.val,by omega⟩)
  apply (p.cHf_le_of_determined (prefixVar X π q) R C ?_).trans
    (p.cHf_fintype_subadd R C)
  intro ω ν hR hcond
  funext i
  by_cases hi : i.val < b
  · have h := congrFun (hC ω ν hcond) i
    simpa [prefixVar,hi,show i.val<q by omega] using h
  by_cases hiq : i.val < q
  · have h := congrFun hR ⟨i.val-b,by omega⟩
    have hidx : (⟨b+(i.val-b), by omega⟩ : Fin k) = i := by
      apply Fin.ext
      change b+(i.val-b)=i.val
      omega
    simpa only [R,hidx,prefixVar,hiq,ite_eq_left] using congrArg some h
  · simp [prefixVar,hiq]

theorem ordered_prefix_conditional_bound {β : Type uBeta} (p : FinLaw Ω)
    (X : Ω → Fin k → α) (C : Equiv.Perm (Fin k) → Ω → β)
    {b q : ℕ} (hbq : b < q) (hq : q ≤ k)
    (hC : ∀ π ω ν, C π ω = C π ν → prefixVar X π b ω = prefixVar X π b ν)
    (hswap : ∀ π (j : Fin k), b ≤ j.val →
      C (π*Equiv.swap ⟨b,by omega⟩ j) = C π) :
    (𝔼 π : Equiv.Perm (Fin k), p.cHf (prefixVar X π q) (C π)) ≤
      (q-b : ℕ) * (𝔼 π : Equiv.Perm (Fin k),
        p.cHf (fun ω => X ω (π ⟨b,by omega⟩)) (C π)) := by
  have h := Finset.expect_le_expect (s := Finset.univ) (fun π _ =>
    p.prefix_conditional_block X π (C π) hbq.le hq (hC π))
  rw [Finset.expect_sum_comm] at h
  have he (j : Fin (q-b)) :
      (𝔼 π : Equiv.Perm (Fin k), p.cHf (fun ω => X ω (π ⟨b+j.val,by omega⟩)) (C π)) =
      𝔼 π : Equiv.Perm (Fin k), p.cHf (fun ω => X ω (π ⟨b,by omega⟩)) (C π) := by
    exact (p.ordered_remaining_exchange_cond X C ⟨b,by omega⟩ ⟨b+j.val,by omega⟩
      (fun π => hswap π _ (by change b ≤ b+j.val; omega))).symm
  simpa only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h

theorem ordered_enrichment_accounting {β : Type uBeta} {γ : Type uGamma} {δ : Type uDelta} (p : FinLaw Ω)
    (X Y Z : Ω → Fin k → α) (d : Ω → Fin k → β) (H : Ω → γ) (E : Ω → δ)
    {b q : ℕ} (hb : 0 < b) (hbq : b < q) (hq : q ≤ k)
    (hd : ∀ i ω ν, X ω i = X ν i → Y ω i = Y ν i → d ω i = d ν i)
    (hY : ∀ i ω ν, X ω i = X ν i → d ω i = d ν i → Y ω i = Y ν i)
    (hH : ∀ i ω ν, H ω = H ν → d ω i = d ν i)
    (hZ : ∀ i ω ν, X ω i = X ν i → E ω = E ν → Z ω i = Z ν i) :
    (b : ℝ) * ((q-b : ℕ) *
      (𝔼 π : Equiv.Perm (Fin k), p.cHf (fun ω => d ω (π ⟨b,by omega⟩))
        (fun ω => (prefixVar X π b ω,prefixVar Y π b ω))) +
      p.orderedEntropy Z q-p.Hf H-p.Hf E) ≤
      (q : ℝ)*(p.orderedEntropy X b+p.orderedEntropy Y b) := by
  let C := fun (π : Equiv.Perm (Fin k)) ω =>
    ((prefixVar X π b ω,prefixVar Y π b ω),H ω)
  let A := 𝔼 π : Equiv.Perm (Fin k),
    p.cHf (fun ω => X ω (π ⟨b,by omega⟩)) (C π)
  let F := 𝔼 π : Equiv.Perm (Fin k),
    p.cHf (fun ω => d ω (π ⟨b,by omega⟩))
      (fun ω => (prefixVar X π b ω,prefixVar Y π b ω))
  have hblock := p.ordered_prefix_conditional_bound X C hbq hq
    (fun π ω ν hh => congrArg (fun c => c.1.1) hh) (by
      intro π j hj
      dsimp [C]
      rw [prefixVar_swap X π b _ j (by exact le_rfl) hj,
        prefixVar_swap Y π b _ j (by exact le_rfl) hj])
  have hlow (π : Equiv.Perm (Fin k)) :
      p.Hf (prefixVar Z π q)-p.Hf E-p.Hf (prefixVar X π b)-
        p.Hf (prefixVar Y π b)-p.Hf H ≤ p.cHf (prefixVar X π q) (C π) := by
    have hz : p.Hf (prefixVar Z π q) ≤ p.Hf (prefixVar X π q)+p.Hf E := by
      apply (p.Hf_le_of_determined (prefixVar Z π q)
        (fun ω => (prefixVar X π q ω,E ω)) ?_).trans (p.Hf_pair_subadd _ _)
      intro ω ν hh
      funext i
      by_cases hi : i.val<q
      · have hx : X ω (π i)=X ν (π i) := by
          simpa [prefixVar,hi] using congrFun (congrArg Prod.fst hh) i
        simpa only [prefixVar,hi,ite_eq_left] using congrArg some
          (hZ (π i) ω ν hx (congrArg Prod.snd hh))
      · simp [prefixVar,hi]
    have hc : p.Hf (C π) ≤ p.Hf (prefixVar X π b)+p.Hf (prefixVar Y π b)+p.Hf H := by
      have h1 := p.Hf_pair_subadd (fun ω => (prefixVar X π b ω,prefixVar Y π b ω)) H
      have h2 := p.Hf_pair_subadd (prefixVar X π b) (prefixVar Y π b)
      dsimp [C]
      linarith
    have hx := p.Hf_pair_ge_snd (C π) (prefixVar X π q)
    rw [p.Hf_pair_comm] at hx
    unfold cHf
    linarith
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun π _ => hlow π)
  simp only [Finset.expect_sub_distrib,Fintype.expect_const] at hav
  have hal : p.orderedEntropy Z q-p.Hf E-p.orderedEntropy X b-
      p.orderedEntropy Y b-p.Hf H ≤ (q-b : ℕ)*A := hav.trans hblock
  have hchain := Finset.expect_le_expect (s := Finset.univ) (fun π _ =>
    p.enrichment_chain (fun ω => X ω (π ⟨b,by omega⟩)) (fun ω => Y ω (π ⟨b,by omega⟩))
      (prefixVar X π b) (prefixVar Y π b) (fun ω => d ω (π ⟨b,by omega⟩)) H
      (hd _) (hY _) (hH _))
  simp only [Finset.expect_sub_distrib,Finset.expect_add_distrib] at hchain
  have hchain' : F ≤ (p.orderedEntropy X (b+1)-p.orderedEntropy X b)+
      (p.orderedEntropy Y (b+1)-p.orderedEntropy Y b)-A := by
    rwa [p.orderedEntropy_step X (by omega),p.orderedEntropy_step Y (by omega)]
  have hx := p.orderedEntropy_slope X hb (by omega)
  have hy := p.orderedEntropy_slope Y hb (by omega)
  have haux : A+F ≤ (p.orderedEntropy X b+p.orderedEntropy Y b)/b := by
    rw [add_div]
    linarith
  have hbR : (0 : ℝ)<b := by exact_mod_cast hb
  have hqR : (0 : ℝ)≤(q-b : ℕ) := by positivity
  have hm := mul_le_mul_of_nonneg_left haux hqR
  have hbmul := mul_le_mul_of_nonneg_left hm hbR.le
  have hn : ((q-b : ℕ) : ℝ) = q-b := by rw [Nat.cast_sub hbq.le]
  have hdiv : (b : ℝ)*((q-b : ℕ)*((p.orderedEntropy X b+p.orderedEntropy Y b)/b)) =
      (q-b : ℕ)*(p.orderedEntropy X b+p.orderedEntropy Y b) := by field_simp
  rw [hdiv] at hbmul
  have hlowmul := mul_le_mul_of_nonneg_left hal hbR.le
  change (b : ℝ)*((q-b : ℕ)*F+p.orderedEntropy Z q-p.Hf H-p.Hf E) ≤ _
  rw [hn] at hbmul hlowmul ⊢
  linarith

end FinLaw

open scoped BigOperators

lemma perm_expect_exchange {ι : Type uIota} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (i j : ι) :
    (𝔼 π : Equiv.Perm ι, f (π i)) = 𝔼 π : Equiv.Perm ι, f (π j) := by
  classical
  apply Fintype.expect_equiv (Equiv.mulRight (Equiv.swap i j))
  intro π
  change f (π i) = f ((π*Equiv.swap i j) j)
  simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_right]

theorem perm_covariance_nonpos {ι : Type uIota} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (hf : ∑ i, f i = 0) {i j : ι} (hij : i ≠ j) :
    (𝔼 π : Equiv.Perm ι, f (π i)*f (π j)) ≤ 0 := by
  classical
  let S := Finset.univ.erase i
  have hS : S.Nonempty := ⟨j,Finset.mem_erase.mpr ⟨hij.symm,Finset.mem_univ _⟩⟩
  have hex (a : ι) (ha : a ∈ S) :
      (𝔼 π : Equiv.Perm ι, f (π i)*f (π a)) =
        𝔼 π : Equiv.Perm ι, f (π i)*f (π j) := by
    have hai : i ≠ a := (Finset.mem_erase.mp ha).1.symm
    apply Fintype.expect_equiv (Equiv.mulRight (Equiv.swap a j))
    intro π
    change f (π i)*f (π a) = f ((π*Equiv.swap a j) i)*f ((π*Equiv.swap a j) j)
    simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hai hij]
  have hsum (π : Equiv.Perm ι) : (∑ a ∈ S, f (π a)) = -f (π i) := by
    have h := Equiv.sum_comp π f
    rw [hf] at h
    have hi := Finset.sum_erase_add (s := Finset.univ) (f := fun a => f (π a))
      (Finset.mem_univ i)
    dsimp [S]
    linarith
  have hid : (S.card : ℝ)*(𝔼 π : Equiv.Perm ι, f (π i)*f (π j)) =
      -(𝔼 π : Equiv.Perm ι, f (π i)^2) := by
    calc
      _ = ∑ a ∈ S, (𝔼 π : Equiv.Perm ι, f (π i)*f (π a)) := by
        rw [show (∑ a ∈ S, (𝔼 π : Equiv.Perm ι, f (π i)*f (π a))) =
            ∑ _a ∈ S, (𝔼 π : Equiv.Perm ι, f (π i)*f (π j)) from
              Finset.sum_congr rfl (fun a ha => hex a ha)]
        simp [nsmul_eq_mul]
      _ = 𝔼 π : Equiv.Perm ι, ∑ a ∈ S, f (π i)*f (π a) :=
        (Finset.expect_sum_comm _ _ _).symm
      _ = -(𝔼 π : Equiv.Perm ι, f (π i)^2) := by
        simp_rw [← Finset.mul_sum,hsum,mul_neg,← sq]
        rw [Finset.expect_neg_distrib]
  have hvar : 0 ≤ (𝔼 π : Equiv.Perm ι, f (π i)^2) :=
    Finset.expect_nonneg (fun _ _ => sq_nonneg _)
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  nlinarith

theorem perm_sample_second_moment {ι : Type uIota} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (hf : ∑ i, f i = 0) (S : Finset ι) {M : ℝ} (hM : ∀ i, (f i)^2 ≤ M) :
    (𝔼 π : Equiv.Perm ι, (∑ i ∈ S, f (π i))^2) ≤ S.card*M := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hsqr (π : Equiv.Perm ι) : (∑ j ∈ insert i S, f (π j))^2 =
        (f (π i))^2+(∑ j ∈ S, f (π j))^2+2*(∑ j ∈ S, f (π i)*f (π j)) := by
      rw [Finset.sum_insert hi,← Finset.mul_sum]
      ring
    simp_rw [hsqr,Finset.expect_add_distrib,← Finset.mul_expect,Finset.expect_sum_comm]
    have hb : (𝔼 π : Equiv.Perm ι, f (π i)^2) ≤ M :=
      (Finset.expect_le_expect (s := Finset.univ) (fun π _ => hM (π i))).trans_eq
        (Fintype.expect_const _)
    have hc : (∑ j ∈ S, (𝔼 π : Equiv.Perm ι, f (π i)*f (π j))) ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      exact perm_covariance_nonpos f hf (fun he => hi (he.symm ▸ hj))
    rw [Finset.card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one]
    linarith

theorem expect_lower_tail_le {Ω : Type uOmega} [Fintype Ω] [Nonempty Ω]
    (Z : Ω → ℝ) {a δ V : ℝ} (hδ : 0 < δ)
    (hV : (𝔼 ω, (Z ω-a)^2) ≤ V) :
    (𝔼 ω, if Z ω < a-δ then (1 : ℝ) else 0) ≤ V/δ^2 := by
  classical
  have he : ∀ ω, δ^2*(if Z ω < a-δ then (1 : ℝ) else 0) ≤ (Z ω-a)^2 := by
    intro ω
    split_ifs with hh
    · nlinarith
    · simpa using sq_nonneg (Z ω-a)
  have h := Finset.expect_le_expect (s := Finset.univ) (fun ω _ => he ω)
  rw [← Finset.mul_expect] at h
  exact (le_div_iff₀ (sq_pos_of_pos hδ)).mpr (by linarith)

theorem perm_sample_interval_tail {ι : Type uIota} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : ι → ℝ) (S : Finset ι) {a M δ : ℝ} (hδ : 0 < δ)
    (hf : ∀ i, a ≤ f i ∧ f i ≤ a+M) :
    (𝔼 π : Equiv.Perm ι,
      if (∑ i ∈ S, f (π i)) < S.card*(𝔼 i, f i)-δ then (1 : ℝ) else 0) ≤
      S.card*M^2/δ^2 := by
  let μ := 𝔼 i, f i
  have hlo : a ≤ μ := by
    have h := Finset.expect_le_expect (s := Finset.univ) (fun i _ => (hf i).1)
    simpa only [Fintype.expect_const] using h
  have hhi : μ ≤ a+M := by
    have h := Finset.expect_le_expect (s := Finset.univ) (fun i _ => (hf i).2)
    simpa only [Fintype.expect_const] using h
  have hsum : ∑ i, (f i-μ) = 0 := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [show (Fintype.card ι : ℝ)*μ = ∑ i, f i from Fintype.card_mul_expect f]
    ring
  have hsq (i : ι) : (f i-μ)^2 ≤ M^2 := by
    have h := hf i
    nlinarith
  have hvar := perm_sample_second_moment (fun i => f i-μ) hsum S hsq
  have hid (π : Equiv.Perm ι) : (∑ i ∈ S, (f (π i)-μ)) =
      (∑ i ∈ S, f (π i))-S.card*μ := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul]
  simp_rw [hid] at hvar
  exact expect_lower_tail_le _ hδ hvar

namespace FinLaw
open scoped BigOperators
variable {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω] {k : ℕ}

noncomputable def uniform (Ω : Type uOmega) [Fintype Ω] [Nonempty Ω] : FinLaw Ω where
  mass := fun _ => (Fintype.card Ω : ℝ)⁻¹
  nonneg := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_one := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω).ne')

@[simp] theorem uniform_mass [Nonempty Ω] (ω : Ω) :
    uniform Ω ω = (Fintype.card Ω : ℝ)⁻¹ := rfl

theorem uniform_Hf_injective {β : Type uBeta} [Nonempty Ω] (X : Ω → β)
    (hX : Function.Injective X) : (uniform Ω).Hf X = Real.log (Fintype.card Ω) := by
  classical
  have hN : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω).ne'
  unfold Hf
  simp only [hX.eq_iff,uniform_mass,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Real.log_inv]
  rw [← mul_assoc,mul_inv_cancel₀ hN]
  ring

theorem Hf_le_log_card_type {β : Type uBeta} [Fintype β] (p : FinLaw Ω) (X : Ω → β) :
    p.Hf X ≤ Real.log (Fintype.card β) := by
  rw [p.Hf_eq_H]
  exact (p.map X).entropy_le_log_card

theorem Hf_le_log_card_set {β : Type uBeta} (p : FinLaw Ω) (X : Ω → β)
    (S : Finset β) (hX : ∀ ω, X ω ∈ S) : p.Hf X ≤ Real.log S.card := by
  classical
  let Y := fun ω => (⟨X ω,hX ω⟩ : S)
  have he : p.Hf X = p.Hf Y := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [he]
  simpa using p.Hf_le_log_card_type Y

theorem map_mix {ι : Type uIota} {β : Type uBeta} [Fintype ι] [Fintype β]
    (p : FinLaw ι) (q : ι → FinLaw Ω) (X : Ω → β) :
    (p.mix q).map X = p.mix (fun i => (q i).map X) := by
  classical
  ext b
  simp only [map_mass,mix_mass,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

theorem Hf_mix_ge {ι : Type uIota} {β : Type uBeta} [Fintype ι]
    (p : FinLaw ι) (q : ι → FinLaw Ω) (X : Ω → β) :
    (∑ i, p i*(q i).Hf X) ≤ (p.mix q).Hf X := by
  classical
  let Y := fun ω => (⟨X ω,⟨ω,rfl⟩⟩ : Set.range X)
  let : Fintype (Set.range X) := Fintype.ofFinite _
  have he (r : FinLaw Ω) : r.Hf X = r.Hf Y := by
    apply r.Hf_eq_of_fibers
    intro ω ν
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  simp_rw [he,Hf_eq_H]
  change (∑ i, p i*((q i).map Y).entropy) ≤ ((p.mix q).map Y).entropy
  rw [map_mix]
  exact p.entropy_mix_ge _

theorem Hf_prefix_le (p : FinLaw Ω) (X : Ω → Fin k → α) (π : Equiv.Perm (Fin k))
    (s : ℕ) : p.Hf (prefixVar X π s) ≤ p.Hf X := by
  exact p.Hf_le_of_determined _ _ (fun ω ν hh =>
    congrArg (fun y (i : Fin k) => if i.val < s then some (y (π i)) else none) hh)

theorem Hf_fintype_subadd {ι : Type uIota} {β : Type uBeta} [Fintype ι] (p : FinLaw Ω)
    (X : Ω → ι → β) : p.Hf X ≤ ∑ i, p.Hf (fun ω => X ω i) := by
  classical
  have he : p.Hf (fun ω (i : (Finset.univ : Finset ι)) => X ω i) = p.Hf X := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    constructor
    · intro hh
      funext i
      exact congrFun hh ⟨i,Finset.mem_univ _⟩
    · intro hh
      funext i
      exact congrFun hh i
  simpa only [he] using p.Hf_finset_subadd X Finset.univ

theorem Hf_prefix_le_sum (p : FinLaw Ω) (X : Ω → Fin k → α)
    (L : Fin k → ℝ) (hL : ∀ i, p.Hf (fun ω => X ω i) ≤ L i)
    (π : Equiv.Perm (Fin k)) {s : ℕ} (hs : s ≤ k) :
    p.Hf (prefixVar X π s) ≤ ∑ j : Fin s, L (π ⟨j.val,by omega⟩) := by
  let Y := fun ω (j : Fin s) => X ω (π ⟨j.val,by omega⟩)
  have he : p.Hf (prefixVar X π s) = p.Hf Y := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    constructor
    · intro hh
      funext j
      have h := congrFun hh ⟨j.val,by omega⟩
      simpa [prefixVar,j.isLt,Y] using h
    · intro hh
      funext j
      by_cases hj : j.val < s
      · have h := congrFun hh ⟨j.val,hj⟩
        simpa [prefixVar,hj,Y] using congrArg some h
      · simp [prefixVar,hj]
  rw [he]
  exact (p.Hf_fintype_subadd Y).trans (Finset.sum_le_sum (fun j _ => hL _))

theorem fresh_entropy_from_prefix {β : Type uBeta} (p : FinLaw Ω)
    (X Y : Ω → Fin k → α) (d : Ω → Fin k → β) {b s : ℕ}
    (hbs : b < s) (hs : s ≤ k)
    (hd : ∀ i ω ν, X ω i = X ν i → Y ω i = Y ν i → d ω i = d ν i) :
    p.orderedEntropy d s-p.orderedEntropy X b-p.orderedEntropy Y b ≤
      (s-b : ℕ)*(𝔼 π : Equiv.Perm (Fin k),
        p.cHf (fun ω => d ω (π ⟨b,by omega⟩))
          (fun ω => (prefixVar X π b ω,prefixVar Y π b ω))) := by
  let C := fun (π : Equiv.Perm (Fin k)) ω => (prefixVar X π b ω,prefixVar Y π b ω)
  have hdet : ∀ π ω ν, C π ω=C π ν → prefixVar d π b ω=prefixVar d π b ν := by
    intro π ω ν hh
    funext i
    by_cases hi : i.val < b
    · have hx := congrFun (congrArg Prod.fst hh) i
      have hy := congrFun (congrArg Prod.snd hh) i
      simp only [C,prefixVar,hi,ite_eq_left,Option.some.injEq] at hx hy
      simpa only [prefixVar,hi,ite_eq_left] using congrArg some (hd (π i) ω ν hx hy)
    · simp [prefixVar,hi]
  have hblock := p.ordered_prefix_conditional_bound d C hbs hs hdet (by
    intro π j hj
    dsimp [C]
    rw [prefixVar_swap X π b _ j (by exact le_rfl) hj,
      prefixVar_swap Y π b _ j (by exact le_rfl) hj])
  have hlow (π : Equiv.Perm (Fin k)) : p.Hf (prefixVar d π s)-
      p.Hf (prefixVar X π b)-p.Hf (prefixVar Y π b) ≤
        p.cHf (prefixVar d π s) (C π) := by
    have h1 := p.Hf_pair_subadd (prefixVar X π b) (prefixVar Y π b)
    have h2 := p.Hf_pair_ge_snd (C π) (prefixVar d π s)
    rw [p.Hf_pair_comm] at h2
    dsimp [C] at *
    unfold cHf
    linarith
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun π _ => hlow π)
  simp only [Finset.expect_sub_distrib] at hav
  exact hav.trans hblock

end FinLaw

end GaussianMoat

end OAI
end
end

section
section
namespace OAI

namespace GaussianMoat
open Filter Topology Finset
open scoped BigOperators

namespace PrimeLogMass
open Filter Topology Finset
open ArithmeticFunction.vonMangoldt Complex
open scoped BigOperators

def dyadicBatch (j : ℕ) : Finset ℕ :=
  (Finset.Ico (2^j) (2^(j+1))).filter (fun p => p.Prime ∧ p % 4 = 1)

lemma mem_dyadicBatch (j p : ℕ) : p ∈ dyadicBatch j ↔
    2^j ≤ p ∧ p < 2^(j+1) ∧ p.Prime ∧ p % 4 = 1 := by
  simp only [dyadicBatch,Finset.mem_filter,Finset.mem_Ico]
  tauto

lemma logBin_mem (p : ℕ) (hp : p.Prime) (hm : p % 4 = 1) :
    p ∈ dyadicBatch (Nat.log 2 p) := by
  rw [mem_dyadicBatch]
  exact ⟨Nat.pow_log_le_self 2 hp.ne_zero,
    Nat.lt_pow_succ_log_self (by norm_num) p,hp,hm⟩

lemma prime_log_mass_le_theta (S : Finset ℕ) {U : ℝ} (hU : 0 ≤ U)
    (hp : ∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ U) :
    (∑ p ∈ S, Real.log p) ≤ Real.log 4*U := by
  apply le_trans _ (Chebyshev.theta_le_log4_mul_x hU)
  rw [Chebyshev.theta_eq_sum_primesLE]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hpS
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.le_floor_iff hU).mpr (hp p hpS).2,(hp p hpS).1⟩
  · intro p hpS _
    exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hpS).2.one_le)

noncomputable def dyadicMass (j : ℕ) : ℝ :=
  ∑ p ∈ dyadicBatch j, Real.log p/p

lemma dyadicMass_nonneg (j : ℕ) : 0 ≤ dyadicMass j := by
  apply Finset.sum_nonneg
  intro p hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast (mem_dyadicBatch _ _ |>.mp hp).2.2.1.one_le))
    (Nat.cast_nonneg _)

lemma dyadicMass_le (j : ℕ) : dyadicMass j ≤ 2*Real.log 4 := by
  have hT : (0 : ℝ) < 2^j := pow_pos (by norm_num) _
  have hs : dyadicMass j ≤ (∑ p ∈ dyadicBatch j, Real.log p)/(2^j : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro p hp
    have h := (mem_dyadicBatch j p).mp hp
    apply div_le_div_of_nonneg_left
    · exact Real.log_nonneg (by exact_mod_cast h.2.2.1.one_le)
    · exact hT
    · exact_mod_cast h.1
  have ht := prime_log_mass_le_theta (dyadicBatch j) (U := (2 : ℝ)^(j+1))
    (by positivity) (by intro p hp; have h := (mem_dyadicBatch j p).mp hp
                        exact ⟨h.2.2.1,by exact_mod_cast h.2.1.le⟩)
  apply hs.trans
  apply (div_le_iff₀ hT).mpr
  rw [pow_succ] at ht
  linarith

lemma dyadicMass_le_card (j : ℕ) : dyadicMass j ≤
    (dyadicBatch j).card * Real.log ((2 : ℝ)^(j+1)) / (2 : ℝ)^j := by
  rw [dyadicMass]
  have hT : (0 : ℝ) < 2^j := pow_pos (by norm_num) _
  have hp (p : ℕ) (hp : p ∈ dyadicBatch j) :
      Real.log p/p ≤ Real.log ((2 : ℝ)^(j+1))/(2 : ℝ)^j := by
    have h := (mem_dyadicBatch j p).mp hp
    apply le_trans (div_le_div_of_nonneg_left
      (Real.log_nonneg (by exact_mod_cast h.2.2.1.one_le)) hT (by exact_mod_cast h.1))
    apply div_le_div_of_nonneg_right _ hT.le
    exact Real.log_le_log (by exact_mod_cast h.2.2.1.pos) (by exact_mod_cast h.2.1.le)
  have hs := Finset.sum_le_sum (s := dyadicBatch j) hp
  simpa [Finset.sum_const,nsmul_eq_mul,mul_div_assoc] using hs

theorem many_dense_bins (J : Finset ℕ) {X c A : ℝ} (hc : 0 < c)
    (hA : 0 < A) (hcard : (J.card : ℝ) ≤ A*X)
    (hmass : c*X ≤ ∑ j ∈ J, dyadicMass j) :
    c*X/(4*Real.log 4) ≤
      ((J.filter (fun j => c/(2*A) ≤ dyadicMass j)).card : ℝ) ∧
    ∀ j ∈ J.filter (fun j => c/(2*A) ≤ dyadicMass j),
      c/(2*A)*(2 : ℝ)^j/Real.log ((2 : ℝ)^(j+1)) ≤ (dyadicBatch j).card := by
  classical
  let G := J.filter (fun j => c/(2*A) ≤ dyadicMass j)
  have hlog : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hδ : 0 < c/(2*A) := div_pos hc (by positivity)
  have ht (j : ℕ) (hj : j ∈ J) : dyadicMass j ≤
      (if j ∈ G then 2*Real.log 4 else 0)+c/(2*A) := by
    by_cases hg : j ∈ G
    · simp only [hg,ite_eq_left]
      linarith [dyadicMass_le j]
    · rw [ite_eq_right hg,zero_add]
      exact (not_le.mp (fun h => hg (Finset.mem_filter.mpr ⟨hj,h⟩))).le
  have hs := Finset.sum_le_sum (s := J) ht
  have he : (∑ j ∈ J, if j ∈ G then 2*Real.log 4 else 0) = G.card*(2*Real.log 4) := by
    rw [← Finset.sum_filter]
    have hG : J.filter (fun j => j ∈ G) = G := by
      ext j
      simp only [G,Finset.mem_filter]
      tauto
    rw [hG]
    simp [nsmul_eq_mul]
  rw [Finset.sum_add_distrib,he,Finset.sum_const,nsmul_eq_mul] at hs
  have hsmall : (J.card : ℝ)*(c/(2*A)) ≤ c*X/2 := by
    have h := mul_le_mul_of_nonneg_right hcard hδ.le
    have he : A*X*(c/(2*A))=c*X/2 := by field_simp
    rwa [he] at h
  refine ⟨(div_le_iff₀ (by positivity)).mpr (by dsimp [G] at hs; linarith),?_⟩
  intro j hj
  have hg := (Finset.mem_filter.mp hj).2
  have h := dyadicMass_le_card j
  have hT : (0 : ℝ) < 2^j := pow_pos (by norm_num) _
  have hL : 0 < Real.log ((2 : ℝ)^(j+1)) := Real.log_pos (one_lt_pow₀ (by norm_num) (by omega))
  apply (div_le_iff₀ hL).mpr
  have h' := (le_div_iff₀ hT).mp (hg.trans h)
  exact h'

noncomputable def splitWindow (X : ℝ) : Finset ℕ :=
  (windowIndices X).filter (fun p => p.Prime ∧ p % 4 = 1)

noncomputable def windowBins (X : ℝ) : Finset ℕ :=
  (splitWindow X).image (Nat.log 2)

lemma split_residue_mass (p : ℕ) (hp : p.Prime) :
    residueClass (1 : ZMod 4) p = if p % 4 = 1 then Real.log p else 0 := by
  have he : (p : ZMod 4) = 1 ↔ p % 4 = 1 := by
    rw [show (1 : ZMod 4) = (1 : ℕ) from rfl,ZMod.natCast_eq_natCast_iff]
    rfl
  simp only [residueClass,Set.indicator_apply,Set.mem_ofPred_eq,he,
    ArithmeticFunction.vonMangoldt_apply_prime hp]

lemma window_mass_le_bins (X : ℝ) :
    (∑ p ∈ (windowIndices X).filter Nat.Prime, residueClass (1 : ZMod 4) p/p) ≤
      ∑ j ∈ windowBins X, dyadicMass j := by
  classical
  have hres : (∑ p ∈ (windowIndices X).filter Nat.Prime, residueClass (1 : ZMod 4) p/p) =
      ∑ p ∈ splitWindow X, Real.log p/p := by
    rw [splitWindow,Finset.sum_filter,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.Prime
    · rw [ite_eq_left hp,split_residue_mass p hp]
      by_cases hm : p % 4=1 <;> simp [hp,hm]
    · simp [hp]
  rw [hres,← Finset.sum_fiberwise_of_maps_to
    (s := splitWindow X) (t := windowBins X) (g := Nat.log 2)
    (fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩)]
  apply Finset.sum_le_sum
  intro j _
  dsimp [dyadicMass]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,hj⟩
    obtain ⟨_,hpp,hpm⟩ := Finset.mem_filter.mp hp
    rw [← hj]
    exact logBin_mem p hpp hpm
  · intro p hp _
    have hpp := ((mem_dyadicBatch j p).mp hp).2.2.1
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_le)) (Nat.cast_nonneg p)

lemma windowBin_bounds {X : ℝ} (hX : 1000 ≤ X) {j : ℕ} (hj : j ∈ windowBins X) :
    X ≤ j*Real.log 2 ∧ j*Real.log 2 ≤ 21/20*X := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨hpW,hpP,hpM⟩ := Finset.mem_filter.mp hp
  have hw := (mem_windowIndices X p).mp hpW
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
  have hlb := (Real.le_log_iff_exp_le hp0).mpr hw.1
  have hub := (Real.log_le_iff_le_exp hp0).mpr hw.2
  have hbin := (mem_dyadicBatch _ _).mp (logBin_mem p hpP hpM)
  have hlow := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ)<2) (Nat.log 2 p))
    (by exact_mod_cast hbin.1 : (2 : ℝ)^Nat.log 2 p ≤ p)
  have hhigh := Real.log_lt_log hp0
    (by exact_mod_cast hbin.2.1 : (p : ℝ) < (2 : ℝ)^(Nat.log 2 p+1))
  rw [Real.log_pow] at hlow hhigh
  simp only [Nat.cast_add,Nat.cast_one] at hhigh
  constructor
  · linarith [Real.log_two_lt_d9]
  · linarith

lemma windowBins_card {X : ℝ} (hX : 1000 ≤ X) : (windowBins X).card ≤ 3*X := by
  classical
  have hX0 : 0 ≤ X := by linarith
  have hs : windowBins X ⊆ Finset.range (⌊2*X⌋₊+1) := by
    intro j hj
    have h := (windowBin_bounds hX hj).2
    have hlog := Real.log_two_gt_d9
    have hj0 : (0 : ℝ)≤j := Nat.cast_nonneg _
    have hjX : (j : ℝ)≤2*X := by nlinarith
    rw [Finset.mem_range,Nat.lt_succ_iff,Nat.le_floor_iff (by positivity : (0 : ℝ)≤2*X)]
    exact hjX
  have hc : (windowBins X).card ≤ ⌊2*X⌋₊+1 :=
    (Finset.card_le_card hs).trans_eq (Finset.card_range _)
  have hcR : ((windowBins X).card:ℝ) ≤ ⌊2*X⌋₊+1 := by exact_mod_cast hc
  have hf := Nat.floor_le (show (0 : ℝ)≤2*X by positivity)
  linarith

theorem eventually_dense_split_bins : ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧
    ∀ᶠ X : ℝ in atTop, ∃ J : Finset ℕ,
      c*X ≤ J.card ∧
      ∀ j ∈ J, X ≤ j*Real.log 2 ∧ j*Real.log 2 ≤ 21/20*X ∧
        δ*(2 : ℝ)^j/Real.log ((2 : ℝ)^(j+1)) ≤ (dyadicBatch j).card := by
  obtain ⟨c,hc,he⟩ := eventually_prime_window_mass (show IsUnit (1 : ZMod 4) from isUnit_one)
  refine ⟨c/(4*Real.log 4),c/6,div_pos hc (by positivity),div_pos hc (by norm_num),?_⟩
  filter_upwards [he,eventually_ge_atTop (1000 : ℝ)] with X hmass hX
  let J := (windowBins X).filter (fun j => c/6 ≤ dyadicMass j)
  have hh := many_dense_bins (windowBins X) hc (by norm_num : (0 : ℝ)<3)
    (windowBins_card hX) (hmass.trans (window_mass_le_bins X))
  refine ⟨J,?_,?_⟩
  · simpa only [show (2 : ℝ)*3=6 by norm_num,div_mul_eq_mul_div] using hh.1
  · intro j hj
    have hb := windowBin_bounds hX (Finset.mem_filter.mp hj).1
    have hd := hh.2 j (by simpa only [show (2 : ℝ)*3=6 by norm_num] using hj)
    exact ⟨hb.1,hb.2,by simpa only [show (2 : ℝ)*3=6 by norm_num] using hd⟩

end PrimeLogMass
end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat
open scoped BigOperators Classical

theorem expect_restrict {κ : Type uKappa} {β : Type uBeta} [Fintype κ] [Fintype β] [Nonempty β]
    (s : Finset κ) (F : (s → β) → ℝ) :
    (𝔼 σ : κ → β, F (fun p => σ p)) = 𝔼 τ : s → β, F τ := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun x => x ∈ s) (fun _ => β)
  calc
    _ = 𝔼 pair : (s → β) × ({x : κ // x ∉ s} → β), F pair.1 := by
      exact Fintype.expect_equiv e _ _ (fun _ => rfl)
    _ = _ := by
      rw [← Finset.univ_product_univ,Finset.expect_product]
      simp only [Fintype.expect_const]

theorem expect_precomp_injective {ι : Type uIota} {κ : Type uKappa} {β : Type uBeta} [Fintype ι] [Fintype κ]
    [Fintype β] [Nonempty β] (e : ι → κ) (he : Function.Injective e)
    (F : (ι → β) → ℝ) :
    (𝔼 σ : κ → β, F (σ ∘ e)) = 𝔼 τ : ι → β, F τ := by
  classical
  let s := Finset.univ.image e
  let ee : ι ≃ s := Equiv.ofBijective (fun i => ⟨e i, Finset.mem_image.mpr
    ⟨i,Finset.mem_univ _,rfl⟩⟩) ⟨fun i j h => he (congrArg Subtype.val h),by
      rintro ⟨y,hy⟩
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hy
      exact ⟨i,Subtype.ext hi⟩⟩
  calc
    _ = 𝔼 τ : s → β, F (fun i => τ (ee i)) := expect_restrict s _
    _ = _ := by
      exact Fintype.expect_equiv (Equiv.arrowCongr ee.symm (Equiv.refl β)) _ _ (fun _ => rfl)

lemma signMeasure_real_eq_expect {ι : Type uIota} [Fintype ι] (S : Set (ι → Bool)) :
    (signMeasure ι).real S = 𝔼 σ : ι → Bool, if σ ∈ S then (1 : ℝ) else 0 := by
  rw [signMeasure_real_set]
  simp [Finset.expect,NNRat.smul_def,div_eq_inv_mul]

lemma expect_sign_restriction {ι : Type uIota} {κ : Type uKappa} [Fintype ι] [Fintype κ]
    (e : ι → κ) (he : Function.Injective e) (S : Set (ι → Bool)) :
    (𝔼 σ : κ → Bool, if σ ∘ e ∈ S then (1 : ℝ) else 0) =
      (signMeasure ι).real S := by
  exact (expect_precomp_injective e he (fun τ => if τ ∈ S then (1 : ℝ) else 0)).trans
    (signMeasure_real_eq_expect S).symm

lemma uniform_entropy_event_bound {Ω : Type uOmega} {Ξ : Type uXi} {α : Type uAlpha} [Fintype Ω] [Nonempty Ω]
    [Fintype Ξ] [Nonempty Ξ] (X : Ξ → Ω → α) (bad : Ξ → Prop)
    (hg : ∀ σ, ¬bad σ → Function.Injective (X σ)) :
    (1-(𝔼 σ, if bad σ then (1 : ℝ) else 0))*Real.log (Fintype.card Ω) ≤
      𝔼 σ, (FinLaw.uniform Ω).Hf (X σ) := by
  have hp (σ : Ξ) : (1-(if bad σ then (1 : ℝ) else 0))*Real.log (Fintype.card Ω) ≤
      (FinLaw.uniform Ω).Hf (X σ) := by
    by_cases hb : bad σ
    · simpa [hb] using (FinLaw.uniform Ω).Hf_nonneg (X σ)
    · simp only [hb,ite_false,sub_zero,one_mul]
      rw [FinLaw.uniform_Hf_injective _ (hg σ hb)]
  have h := Finset.expect_le_expect (s := Finset.univ) (fun σ _ => hp σ)
  simpa only [← Finset.expect_mul,Finset.expect_sub_distrib,Fintype.expect_const] using h

abbrev SplitSieve.restrict (s : SplitSieve) (Q : Finset ℕ) (hQ : Q ⊆ s.primes) : SplitSieve where
  primes := Q
  factor := s.factor
  prime_mem := fun p hp => s.prime_mem p (hQ hp)
  mod_four := fun p hp => s.mod_four p (hQ hp)
  factor_irreducible := fun p hp => s.factor_irreducible p (hQ hp)
  factor_norm := fun p hp => s.factor_norm p (hQ hp)

noncomputable def SplitSieve.enumeration (s : SplitSieve) : Fin s.primes.card ≃ s.primes :=
  s.primes.equivFin.symm

noncomputable def prefixIndices (k r : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => i.val < r)

lemma mem_prefixIndices {k r : ℕ} (i : Fin k) : i ∈ prefixIndices k r ↔ i.val < r := by
  simp [prefixIndices]

lemma prefixIndices_card {k r : ℕ} (hr : r ≤ k) : (prefixIndices k r).card = r := by
  have he : prefixIndices k r = (Finset.univ : Finset (Fin r)).image
      (fun i => (⟨i.val,by omega⟩ : Fin k)) := by
    ext i
    simp only [mem_prefixIndices,Finset.mem_image,Finset.mem_univ,true_and]
    exact ⟨fun hi => ⟨⟨i.val,hi⟩,rfl⟩,fun ⟨j,hj⟩ => by cases hj; exact j.isLt⟩
  have hinj : Function.Injective (fun i : Fin r => (⟨i.val,by omega⟩ : Fin k)) :=
    fun i j h => Fin.ext (congrArg (fun j : Fin k => j.val) h)
  rw [he,Finset.card_image_of_injective _ hinj]
  exact Finset.card_fin r

noncomputable def SplitSieve.prefixSet (s : SplitSieve)
    (π : Equiv.Perm (Fin s.primes.card)) (r : ℕ) : Finset ℕ :=
  (prefixIndices s.primes.card r).image (fun i => (s.enumeration (π i)).val)

lemma SplitSieve.prefixSet_subset (s : SplitSieve)
    (π : Equiv.Perm (Fin s.primes.card)) (r : ℕ) : s.prefixSet π r ⊆ s.primes := by
  intro p hp
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
  exact (s.enumeration (π i)).property

lemma SplitSieve.prefixSet_card (s : SplitSieve)
    (π : Equiv.Perm (Fin s.primes.card)) {r : ℕ} (hr : r ≤ s.primes.card) :
    (s.prefixSet π r).card = r := by
  have hinj : Function.Injective (fun i => (s.enumeration (π i)).val) :=
    Subtype.val_injective.comp (s.enumeration.injective.comp π.injective)
  rw [SplitSieve.prefixSet,Finset.card_image_of_injective _ hinj]
  exact prefixIndices_card hr

noncomputable abbrev SplitSieve.prefixSieve (s : SplitSieve)
    (π : Equiv.Perm (Fin s.primes.card)) (r : ℕ) : SplitSieve :=
  s.restrict (s.prefixSet π r) (s.prefixSet_subset π r)

noncomputable def SplitSieve.residueVector (s : SplitSieve)
    (σ : Fin s.primes.card → Bool) (z : GaussianInt) (i : Fin s.primes.card) : ℕ :=
  residueCode (signedFactor (s.factor (s.enumeration i)) (σ i)) z

noncomputable def SplitSieve.prefixIndex (s : SplitSieve)
    (π : Equiv.Perm (Fin s.primes.card)) (r : ℕ) (p : (s.prefixSet π r)) : Fin s.primes.card :=
  s.enumeration.symm ⟨p.val,s.prefixSet_subset π r p.property⟩

lemma SplitSieve.prefixIndex_injective (s : SplitSieve)
    (π : Equiv.Perm (Fin s.primes.card)) (r : ℕ) : Function.Injective (s.prefixIndex π r) := by
  intro p q hpq
  apply Subtype.ext
  exact congrArg (fun y : s.primes => (y : ℕ)) (s.enumeration.symm.injective hpq)

lemma SplitSieve.prefix_injective_of_no_bad (s : SplitSieve)
    (π : Equiv.Perm (Fin s.primes.card)) (r : ℕ)
    (σ : Fin s.primes.card → Bool) (Δ : Finset GaussianInt) (Q : Set GaussianInt)
    (hΔ : ∀ x ∈ Δ, ∀ y ∈ Δ, x-y ∈ Q)
    (hb : ¬(s.prefixSieve π r).badSign Q (σ ∘ s.prefixIndex π r)) :
    Function.Injective (fun x : Δ => FinLaw.prefixVar (fun x : Δ => s.residueVector σ x) π r x) := by
  intro x y hxy
  apply Subtype.ext
  by_contra hne
  apply hb
  refine ⟨x-y,hΔ x x.property y y.property,sub_ne_zero.mpr hne,?_⟩
  apply (s.prefixSieve π r).prod_factors_dvd _ (fun _ h => h)
  intro p hp
  obtain ⟨i,hi,hp'⟩ := Finset.mem_image.mp hp
  have hres := congrFun hxy i
  have hiv := (mem_prefixIndices i).mp hi
  simp only [FinLaw.prefixVar,hiv,ite_eq_left,Option.some.injEq] at hres
  have hidx : s.prefixIndex π r ⟨p,hp⟩ = π i := by
    apply s.enumeration.injective
    apply Subtype.ext
    simpa only [SplitSieve.prefixIndex,Equiv.apply_symm_apply] using hp'.symm
  rw [SplitSieve.extendSigns_mem _ _ p hp]
  change signedFactor (s.factor p) (σ (s.prefixIndex π r ⟨p,hp⟩)) ∣ _
  rw [hidx]
  simpa only [SplitSieve.residueVector,hp'] using
      (residueCode_eq _ _ _).mp hres

theorem SplitSieve.prefix_entropy_rectangle (s : SplitSieve)
    (π : Equiv.Perm (Fin s.primes.card)) {r : ℕ} (hr : r ≤ s.primes.card)
    (Δ : Finset GaussianInt) (hΔne : Δ.Nonempty)
    {T R W d : ℝ} {e : ℂ} (he : ‖e‖=1) (hT : 5 ≤ T)
    (hpT : ∀ p ∈ s.primes, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hd : 0 < d) (hd1 : d < 1/4)
    (harea : R*W ≤ ((s.prefixSieve π r).period : ℝ)^(1-d))
    (hlarge : 1000 ≤ d^3*r)
    (hΔ : ∀ x ∈ Δ, ∀ y ∈ Δ, x-y ∈ orientedRectangle e R W) :
    let := hΔne.to_subtype
    (1-Real.exp (-(d^3*r/5120)))*Real.log Δ.card ≤
      𝔼 σ : Fin s.primes.card → Bool,
        (FinLaw.uniform Δ).Hf (FinLaw.prefixVar (fun x : Δ => s.residueVector σ x) π r) := by
  let := hΔne.to_subtype
  let t := s.prefixSieve π r
  let Q := orientedRectangle e R W
  have hc : t.primes.card=r := s.prefixSet_card π hr
  have hprob : (𝔼 σ : Fin s.primes.card → Bool,
      if t.badSign Q (σ ∘ s.prefixIndex π r) then (1 : ℝ) else 0) ≤
      Real.exp (-(d^3*r/5120)) := by
    calc
      _ = (signMeasure t.primes).real {τ | t.badSign Q τ} := by
        convert expect_sign_restriction (s.prefixIndex π r) (s.prefixIndex_injective π r)
          {τ | t.badSign Q τ} using 1
        congr 1
        ext σ; simp
      _ ≤ _ := by
        have ht := t.signed_rectangle he hT (fun p hp => hpT p (s.prefixSet_subset π r hp))
          hW hWR hd hd1 harea (by rwa [hc])
        simpa only [hc] using ht
  have hg := uniform_entropy_event_bound
    (fun σ => FinLaw.prefixVar (fun x : Δ => s.residueVector σ x) π r)
    (fun σ => t.badSign Q (σ ∘ s.prefixIndex π r))
    (fun σ hb => s.prefix_injective_of_no_bad π r σ Δ Q hΔ hb)
  simp only [Fintype.card_coe] at hg
  have hl : 0 ≤ Real.log (Δ.card : ℝ) := Real.log_nonneg (by exact_mod_cast hΔne.card_pos)
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hprob 1) hl).trans hg

noncomputable def SplitSieve.meanLog (s : SplitSieve) : ℝ :=
  𝔼 i : Fin s.primes.card, Real.log (s.enumeration i : ℕ)

lemma SplitSieve.prefix_log_period (s : SplitSieve)
    (π : Equiv.Perm (Fin s.primes.card)) (r : ℕ) :
    Real.log ((s.prefixSieve π r).period : ℝ) =
      ∑ i ∈ prefixIndices s.primes.card r, Real.log (s.enumeration (π i) : ℕ) := by
  rw [SplitSieve.log_period]
  rw [Finset.sum_coe_sort (s.prefixSieve π r).primes (fun p : ℕ => Real.log (p : ℝ))]
  change (∑ p ∈ s.prefixSet π r, Real.log (p : ℝ)) = _
  unfold SplitSieve.prefixSet
  exact Finset.sum_image (Subtype.val_injective.comp
    (s.enumeration.injective.comp π.injective)).injOn

lemma SplitSieve.prefix_product_tail (s : SplitSieve) (hk : 0 < s.primes.card)
    {r : ℕ} (hr : r ≤ s.primes.card) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hpT : ∀ p ∈ s.primes, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T) :
    (𝔼 π : Equiv.Perm (Fin s.primes.card),
      if Real.log ((s.prefixSieve π r).period : ℝ) < r*s.meanLog-δ then (1 : ℝ) else 0) ≤
      r*(Real.log 2)^2/δ^2 := by
  let : Nonempty (Fin s.primes.card) := ⟨⟨0,hk⟩⟩
  have hb (i : Fin s.primes.card) : Real.log T ≤ Real.log (s.enumeration i : ℕ) ∧
      Real.log (s.enumeration i : ℕ) ≤ Real.log T+Real.log 2 := by
    have hh := hpT (s.enumeration i) (s.enumeration i).property
    constructor
    · exact Real.log_le_log hT hh.1
    · have h := Real.log_le_log (hT.trans_le hh.1) hh.2
      rwa [Real.log_mul (by norm_num : (2 : ℝ)≠0) hT.ne',add_comm] at h
  have h := perm_sample_interval_tail (fun i => Real.log (s.enumeration i : ℕ))
    (prefixIndices s.primes.card r) hδ hb
  convert h using 1 <;>
    simp only [prefixIndices_card hr,SplitSieve.meanLog,← s.prefix_log_period]
  congr 1

theorem SplitSieve.signed_prefix_entropy (s : SplitSieve)
    {r : ℕ} (hr : r ≤ s.primes.card) (Δ : Finset GaussianInt) (hΔne : Δ.Nonempty)
    {T R W d δ : ℝ} {e : ℂ} (he : ‖e‖=1) (hT : 5 ≤ T)
    (hpT : ∀ p ∈ s.primes, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hd : 0 < d) (hd1 : d < 1/4)
    (hδ : 0 < δ) (hgap : Real.log (R*W) ≤ (1-d)*(r*s.meanLog-δ))
    (hlarge : 1000 ≤ d^3*r)
    (hΔ : ∀ x ∈ Δ, ∀ y ∈ Δ, x-y ∈ orientedRectangle e R W) :
    let := hΔne.to_subtype
    (1-r*(Real.log 2)^2/δ^2-Real.exp (-(d^3*r/5120)))*Real.log Δ.card ≤
      (FinLaw.uniform Δ).signedEntropy (fun σ x => s.residueVector σ x) r := by
  let := hΔne.to_subtype
  have hk : 0 < s.primes.card := by
    by_contra hn
    have hz : r=0 := by omega
    simp only [hz,Nat.cast_zero,mul_zero] at hlarge
    norm_num at hlarge
  have hRW : 0 < R*W := mul_pos (by linarith) (by linarith)
  have hlog : 0 ≤ Real.log (Δ.card : ℝ) := Real.log_nonneg (by exact_mod_cast hΔne.card_pos)
  let ε := Real.exp (-(d^3*r/5120))
  let bad (π : Equiv.Perm (Fin s.primes.card)) :=
    Real.log ((s.prefixSieve π r).period : ℝ) < r*s.meanLog-δ
  have hp (π : Equiv.Perm (Fin s.primes.card)) :
      (1-(if bad π then (1 : ℝ) else 0)-ε)*Real.log Δ.card ≤
      𝔼 σ : Fin s.primes.card → Bool,
        (FinLaw.uniform Δ).Hf (FinLaw.prefixVar (fun x : Δ => s.residueVector σ x) π r) := by
    by_cases hb : bad π
    · have hn : 0 ≤ (𝔼 σ : Fin s.primes.card → Bool,
          (FinLaw.uniform Δ).Hf (FinLaw.prefixVar (fun x : Δ => s.residueVector σ x) π r)) :=
        Finset.expect_nonneg (fun _ _ => (FinLaw.uniform Δ).Hf_nonneg _)
      simp only [hb,ite_eq_left,sub_self,zero_sub]
      exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le) hlog).trans hn
    · simp only [hb,ite_false,sub_zero]
      apply s.prefix_entropy_rectangle π hr Δ hΔne he hT hpT hW hWR hd hd1 ?_ hlarge hΔ
      have hP : 0 < ((s.prefixSieve π r).period : ℝ) := by
        exact_mod_cast (s.prefixSieve π r).period_pos
      apply (Real.log_le_log_iff hRW (Real.rpow_pos_of_pos hP _)).mp
      rw [Real.log_rpow hP]
      exact hgap.trans (mul_le_mul_of_nonneg_left (le_of_not_gt hb) (by linarith))
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun π _ => hp π)
  simp only [← Finset.expect_mul,Finset.expect_sub_distrib,Fintype.expect_const] at hav
  have hb := s.prefix_product_tail hk hr (by linarith : (0 : ℝ)<T) hδ hpT
  have hlow := mul_le_mul_of_nonneg_right (sub_le_sub_right (sub_le_sub_left hb 1) ε) hlog
  apply hlow.trans
  convert hav using 1
  unfold FinLaw.signedEntropy FinLaw.orderedEntropy
  exact Finset.expect_comm _ _ _

lemma SplitSieve.residueVector_entropy_le {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve) (P : FinLaw Ω) (Z : Ω → GaussianInt)
    (σ : Fin s.primes.card → Bool) (i : Fin s.primes.card) :
    P.Hf (fun ω => s.residueVector σ (Z ω) i) ≤ Real.log (s.enumeration i : ℕ) := by
  let π := signedFactor (s.factor (s.enumeration i)) (σ i)
  have hπ : π ≠ 0 := (signedFactor_irreducible
    (s.factor_irreducible _ (s.enumeration i).property) _).ne_zero
  obtain ⟨hfin,hcard⟩ := residueCode_range_card hπ
  have h := P.Hf_le_log_card_set (fun ω => residueCode π (Z ω)) hfin.toFinset
    (fun ω => hfin.mem_toFinset.mpr ⟨Z ω,rfl⟩)
  rw [← Set.ncard_eq_toFinset_card (Set.range (residueCode π)) hfin,hcard] at h
  have hn : π.norm.natAbs=(s.enumeration i : ℕ) := by
    dsimp [π]
    rw [signedFactor_norm,s.factor_norm _ (s.enumeration i).property,Int.natAbs_natCast]
  rw [hn] at h
  exact h

lemma SplitSieve.residue_prefix_entropy_le {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve) (P : FinLaw Ω) (Z : Ω → GaussianInt)
    (σ : Fin s.primes.card → Bool) {b : ℕ} (hb : b ≤ s.primes.card)
    {U : ℝ} (hU : ∀ p ∈ s.primes, Real.log (p : ℝ) ≤ U) :
    P.orderedEntropy (fun ω => s.residueVector σ (Z ω)) b ≤ b*U := by
  have h (π : Equiv.Perm (Fin s.primes.card)) := P.Hf_prefix_le_sum
    (fun ω => s.residueVector σ (Z ω)) (fun _ => U)
    (fun i => (s.residueVector_entropy_le P Z σ i).trans
      (hU _ (s.enumeration i).property)) π hb
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun π _ => h π)
  simpa only [FinLaw.orderedEntropy,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Fintype.expect_const] using hh

theorem SplitSieve.actual_fresh_entropy (s : SplitSieve)
    {b r : ℕ} (hbr : b < r) (hr : r ≤ s.primes.card)
    (Δ : Finset GaussianInt) (hΔne : Δ.Nonempty)
    (X Y : Δ → GaussianInt) (hXY : ∀ ω, X ω-Y ω=ω)
    {T R W d δ : ℝ} {e : ℂ} (he : ‖e‖=1) (hT : 5 ≤ T)
    (hpT : ∀ p ∈ s.primes, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hd : 0 < d) (hd1 : d < 1/4)
    (hδ : 0 < δ) (hgap : Real.log (R*W) ≤ (1-d)*(r*s.meanLog-δ))
    (hlarge : 1000 ≤ d^3*r)
    (hΔ : ∀ x ∈ Δ, ∀ y ∈ Δ, x-y ∈ orientedRectangle e R W) :
    let := hΔne.to_subtype
    (1-r*(Real.log 2)^2/δ^2-Real.exp (-(d^3*r/5120)))*Real.log Δ.card-
        2*b*Real.log (2*T) ≤
      (r-b : ℕ)*(𝔼 σ : Fin s.primes.card → Bool,
        𝔼 π : Equiv.Perm (Fin s.primes.card),
          (FinLaw.uniform Δ).cHf (fun ω => s.residueVector σ ω (π ⟨b,by omega⟩))
            (fun ω => (FinLaw.prefixVar (fun x => s.residueVector σ (X x)) π b ω,
              FinLaw.prefixVar (fun x => s.residueVector σ (Y x)) π b ω))) := by
  let := hΔne.to_subtype
  let P := FinLaw.uniform Δ
  have hU (p : ℕ) (hp : p ∈ s.primes) : Real.log (p : ℝ) ≤ Real.log (2*T) :=
    Real.log_le_log (by have := (hpT p hp).1; linarith) (hpT p hp).2
  have hp (σ : Fin s.primes.card → Bool) := P.fresh_entropy_from_prefix
    (fun ω => s.residueVector σ (X ω)) (fun ω => s.residueVector σ (Y ω))
    (fun ω => s.residueVector σ ω) hbr hr (by
      intro i ω ν hx hy
      change residueCode _ (ω : GaussianInt) = residueCode _ (ν : GaussianInt)
      rw [← hXY ω,← hXY ν]
      exact residueCode_sub hx hy)
  have hX σ := s.residue_prefix_entropy_le P X σ (by omega : b ≤ s.primes.card) hU
  have hY σ := s.residue_prefix_entropy_le P Y σ (by omega : b ≤ s.primes.card) hU
  have hl (σ : Fin s.primes.card → Bool) :
      P.orderedEntropy (fun ω => s.residueVector σ ω) r-2*b*Real.log (2*T) ≤
      (r-b : ℕ)*(𝔼 π : Equiv.Perm (Fin s.primes.card),
        P.cHf (fun ω => s.residueVector σ ω (π ⟨b,by omega⟩))
          (fun ω => (FinLaw.prefixVar (fun x => s.residueVector σ (X x)) π b ω,
            FinLaw.prefixVar (fun x => s.residueVector σ (Y x)) π b ω))) := by
    linarith [hp σ,hX σ,hY σ]
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun σ _ => hl σ)
  simp only [Finset.expect_sub_distrib,Fintype.expect_const,← Finset.mul_expect] at hh
  have hg := s.signed_prefix_entropy hr Δ hΔne he hT hpT hW hWR hd hd1 hδ hgap hlarge hΔ
  exact (sub_le_sub_right hg _).trans hh

end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat

section
open scoped BigOperators Classical

theorem latticeBall_card_le {R : ℝ} (hR : 1 ≤ R) :
    ((latticeBall R).card : ℝ) ≤ 36*R^2 := by
  have h := lattice_rectangle_card (latticeBall R) (e := 1) (c := (-R : ℝ))
    (by simp) (R := 2*R) (by linarith) hR (by
      intro z hz
      have hn := (mem_latticeBall R z).mp hz
      have hr := abs_le.mp ((Complex.abs_re_le_norm (z:ℂ)).trans hn)
      have hi := (Complex.abs_im_le_norm (z:ℂ)).trans hn
      simp only [one_mul,Complex.sub_re,Complex.ofReal_re,sub_neg_eq_add,
        Complex.sub_im,Complex.ofReal_im,sub_zero]
      exact ⟨by linarith,by linarith,hi⟩)
  linarith

theorem displacement_entropy_le {Ω : Type uOmega} [Fintype Ω] (P : FinLaw Ω)
    (Z : Ω → GaussianInt) {R : ℝ} (hR : 1 ≤ R) (hZ : ∀ ω, ‖(Z ω:ℂ)‖ ≤ R) :
    P.Hf Z ≤ Real.log 36+2*Real.log R := by
  have h := P.Hf_le_log_card_set Z (latticeBall R) (fun ω => (mem_latticeBall R _).mpr (hZ ω))
  have hc : 0 < ((latticeBall R).card:ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨0,by simpa using (show 0 ≤ R by linarith)⟩
  have hl := Real.log_le_log hc (latticeBall_card_le hR)
  rw [Real.log_mul (by norm_num : (36:ℝ)≠0) (pow_ne_zero _ (by linarith : R≠0)),
    Real.log_pow] at hl
  exact h.trans hl

theorem differences_rectangle (E : Finset GaussianInt) {e c : ℂ} {R W : ℝ}
    (hE : ∀ p ∈ E, 0 ≤ (e*((p:ℂ)-c)).re ∧
      (e*((p:ℂ)-c)).re ≤ R ∧ |(e*((p:ℂ)-c)).im| ≤ W) :
    ∀ x ∈ differences E, ∀ y ∈ differences E,
      x-y ∈ orientedRectangle (star e) (4*R) (4*W) := by
  intro x hx y hy
  obtain ⟨a,ha,b,hb,rfl⟩ := (mem_differences E x).mp hx
  obtain ⟨a',ha',b',hb',rfl⟩ := (mem_differences E y).mp hy
  have h1 := hE a ha
  have h2 := hE b hb
  have h3 := hE a' ha'
  have h4 := hE b' hb'
  have heq : e*((a:ℂ)-(b:ℂ)-((a':ℂ)-(b':ℂ))) =
      e*((a:ℂ)-c)-e*((b:ℂ)-c)-(e*((a':ℂ)-c)-e*((b':ℂ)-c)) := by ring
  rw [orientedRectangle]
  simp only [Set.mem_ofPred_eq,star_star,map_sub,heq,Complex.sub_re,Complex.sub_im]
  obtain ⟨h1i,h1i'⟩ := abs_le.mp h1.2.2
  obtain ⟨h2i,h2i'⟩ := abs_le.mp h2.2.2
  obtain ⟨h3i,h3i'⟩ := abs_le.mp h3.2.2
  obtain ⟨h4i,h4i'⟩ := abs_le.mp h4.2.2
  refine ⟨abs_le.mpr ⟨?_,?_⟩,abs_le.mpr ⟨?_,?_⟩⟩ <;> linarith

lemma difference_exists_pair (z : ℕ → GaussianInt) (n : ℕ)
    (d : differences (walkSegment z n)) :
    ∃ ij : Fin (n+1) × Fin (n+1), z ij.1.val-z ij.2.val=d := by
  obtain ⟨a,ha,b,hb,hab⟩ := (mem_differences _ _).mp d.property
  obtain ⟨i,hi,rfl⟩ := (mem_walkSegment _ _ _).mp ha
  obtain ⟨j,hj,rfl⟩ := (mem_walkSegment _ _ _).mp hb
  exact ⟨(⟨i,by omega⟩,⟨j,by omega⟩),hab⟩

noncomputable def differenceRepresentative (z : ℕ → GaussianInt) (n : ℕ)
    (d : differences (walkSegment z n)) : Fin (n+1) × Fin (n+1) :=
  (difference_exists_pair z n d).choose

lemma differenceRepresentative_spec (z : ℕ → GaussianInt) (n : ℕ)
    (d : differences (walkSegment z n)) :
    z (differenceRepresentative z n d).1.val-z (differenceRepresentative z n d).2.val=d :=
  (difference_exists_pair z n d).choose_spec

lemma differenceRepresentative_injective (z : ℕ → GaussianInt) (n : ℕ) :
    Function.Injective (differenceRepresentative z n) := by
  intro d d' hh
  apply Subtype.ext
  rw [← differenceRepresentative_spec z n d,← differenceRepresentative_spec z n d',hh]

lemma differences_walkSegment_nonempty (z : ℕ → GaussianInt) (n : ℕ) :
    (differences (walkSegment z n)).Nonempty := by
  refine ⟨0,(mem_differences _ _).mpr ⟨z 0,?_,z 0,?_,sub_self _⟩⟩ <;>
    exact (mem_walkSegment _ _ _).mpr ⟨0,by omega,rfl⟩

end

namespace FinLaw
open scoped BigOperators Classical
variable {ι : Type uIota} {Ω : Type uOmega} {κ : Type uKappa} {α : Type uAlpha} {β : Type uBeta} [Fintype ι] [Fintype Ω] [Fintype κ]

noncomputable def joint (p : FinLaw ι) (q : ι → FinLaw Ω) : FinLaw (ι × Ω) where
  mass := fun v => p v.1*q v.1 v.2
  nonneg := fun v => mul_nonneg (p.nonneg _) ((q _).nonneg _)
  sum_one := by
    simp only [Fintype.sum_prod_type,← Finset.mul_sum,FinLaw.sum_one,mul_one]

@[simp] theorem joint_mass (p : FinLaw ι) (q : ι → FinLaw Ω) (i : ι) (ω : Ω) :
    p.joint q (i,ω) = p i*q i ω := rfl

@[simp] theorem joint_map_fst (p : FinLaw ι) (q : ι → FinLaw Ω) :
    (p.joint q).map Prod.fst = p := by
  ext i
  simp only [map_mass,Fintype.sum_prod_type,joint_mass]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,← Finset.mul_sum,
    sum_one,mul_one]

@[simp] theorem joint_map_snd (p : FinLaw ι) (q : ι → FinLaw Ω) :
    (p.joint q).map Prod.snd = p.mix q := by
  ext ω
  simp [map_mass,Fintype.sum_prod_type,joint_mass,mix_mass]

@[simp] theorem joint_map_second (p : FinLaw ι) (q : ι → FinLaw Ω) (f : Ω → κ) :
    (p.joint q).map (fun v => (v.1,f v.2)) = p.joint (fun i => (q i).map f) := by
  ext ⟨i,x⟩
  simp only [map_mass,Fintype.sum_prod_type,joint_mass,Prod.mk.injEq,ite_and]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

theorem entropy_joint (p : FinLaw ι) (q : ι → FinLaw Ω) :
    (p.joint q).entropy = p.entropy+∑ i, p i*(q i).entropy := by
  simp only [entropy,entropySum,Fintype.sum_prod_type,joint_mass,Real.negMulLog_mul,
    Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,FinLaw.sum_one,one_mul]

theorem Hf_map (p : FinLaw Ω) (f : Ω → κ) (X : κ → α) :
    (p.map f).Hf X = p.Hf (X ∘ f) := by
  rw [Hf_code,H,map_comp]
  rw [← H,← Hf_eq_H]
  apply p.Hf_eq_of_fibers
  intro ω ν
  exact outputCode_eq_iff X (f ω) (f ν)

theorem cHf_map (p : FinLaw Ω) (f : Ω → κ) (X : κ → α) (Y : κ → β) :
    (p.map f).cHf X Y = p.cHf (X ∘ f) (Y ∘ f) := by
  simp only [cHf,Hf_map,Function.comp_def]

theorem Hf_joint_pair (p : FinLaw ι) (q : ι → FinLaw Ω) (X : Ω → α) :
    (p.joint q).Hf (fun v => (v.1,X v.2)) = p.entropy+∑ i, p i*(q i).Hf X := by
  let C := outputCode X
  have he (r : FinLaw Ω) : r.Hf X = r.Hf C :=
    r.Hf_eq_of_fibers X C (fun ω ν => (outputCode_eq_iff X ω ν).symm)
  have he' : (p.joint q).Hf (fun v => (v.1,X v.2)) =
      (p.joint q).Hf (fun v => (v.1,C v.2)) := by
    apply Hf_eq_of_fibers
    intro v w
    simp only [Prod.mk.injEq,C,outputCode_eq_iff]
  rw [he',Hf_eq_H,H,joint_map_second,entropy_joint]
  simp_rw [he,Hf_eq_H,H]

theorem cHf_mix_ge (p : FinLaw ι) (q : ι → FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    (∑ i, p i*(q i).cHf X Y) ≤ (p.mix q).cHf X Y := by
  have hm := (p.joint q).cHf_mono (fun v => X v.2) (fun v => Y v.2) Prod.fst
  have hid : (p.joint q).cHf (fun v => X v.2) (fun v => (Y v.2,v.1)) =
      ∑ i, p i*(q i).cHf X Y := by
    unfold cHf
    have h1 : (p.joint q).Hf (fun v => (X v.2,(Y v.2,v.1))) =
        (p.joint q).Hf (fun v => (v.1,(X v.2,Y v.2))) := by
      apply Hf_eq_of_fibers
      intro v w
      simp only [Prod.mk.injEq]
      tauto
    rw [h1,Hf_joint_pair p q (fun ω => (X ω,Y ω)),
      Hf_pair_comm (p.joint q) (fun v => Y v.2) Prod.fst, Hf_joint_pair]
    simp only [mul_sub,Finset.sum_sub_distrib]
    ring
  rw [hid] at hm
  have he := (p.joint q).cHf_map Prod.snd X Y
  rw [joint_map_snd] at he
  exact hm.trans_eq he.symm

theorem joint_map_fiber (p : FinLaw ι) (q : ι → FinLaw Ω) (f : ι → Ω → κ) :
    (p.joint q).map (fun v => (v.1,f v.1 v.2)) = p.joint (fun i => (q i).map (f i)) := by
  ext ⟨i,x⟩
  simp only [map_mass,Fintype.sum_prod_type,joint_mass,Prod.mk.injEq,ite_and]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

theorem Hf_joint_pair_vary (p : FinLaw ι) (q : ι → FinLaw Ω) (X : ι → Ω → α) :
    (p.joint q).Hf (fun v => (v.1,X v.1 v.2)) =
      p.entropy+∑ i, p i*(q i).Hf (X i) := by
  let C := outputCode (fun v : ι × Ω => X v.1 v.2)
  have he (i : ι) : (q i).Hf (X i) = (q i).Hf (fun ω => C (i,ω)) := by
    apply Hf_eq_of_fibers
    intro ω ν
    exact (outputCode_eq_iff (fun v : ι × Ω => X v.1 v.2) (i,ω) (i,ν)).symm
  have he' : (p.joint q).Hf (fun v => (v.1,X v.1 v.2)) =
      (p.joint q).Hf (fun v => (v.1,C v)) := by
    apply Hf_eq_of_fibers
    intro v w
    simp only [Prod.mk.injEq,C,outputCode_eq_iff]
  rw [he',Hf_eq_H,H,joint_map_fiber p q (fun i ω => C (i,ω)),entropy_joint]
  simp_rw [he,Hf_eq_H,H]

theorem cHf_joint_ge (p : FinLaw ι) (q : ι → FinLaw Ω)
    (X : ι → Ω → α) (Y : ι → Ω → β) :
    (∑ i, p i*(q i).cHf (X i) (Y i)) ≤
      (p.joint q).cHf (fun v => X v.1 v.2) (fun v => Y v.1 v.2) := by
  have hm := (p.joint q).cHf_mono (fun v => X v.1 v.2) (fun v => Y v.1 v.2) Prod.fst
  have hid : (p.joint q).cHf (fun v => X v.1 v.2) (fun v => (Y v.1 v.2,v.1)) =
      ∑ i, p i*(q i).cHf (X i) (Y i) := by
    unfold cHf
    have h1 : (p.joint q).Hf (fun v => (X v.1 v.2,(Y v.1 v.2,v.1))) =
        (p.joint q).Hf (fun v => (v.1,(X v.1 v.2,Y v.1 v.2))) := by
      apply Hf_eq_of_fibers
      intro v w
      simp only [Prod.mk.injEq]
      tauto
    rw [h1,Hf_joint_pair_vary p q (fun i ω => (X i ω,Y i ω)),
      Hf_pair_comm (p.joint q) (fun v => Y v.1 v.2) Prod.fst,Hf_joint_pair_vary]
    simp only [mul_sub,Finset.sum_sub_distrib]
    ring
  rwa [hid] at hm

theorem Hf_pair_const_right (p : FinLaw Ω) (X : Ω → α) (c : β) :
    p.Hf (fun ω => (X ω,c)) = p.Hf X := by
  apply Hf_eq_of_fibers
  intro ω ν
  simp

theorem Hf_joint_ge (p : FinLaw ι) (q : ι → FinLaw Ω) (X : ι → Ω → α) :
    (∑ i, p i*(q i).Hf (X i)) ≤ (p.joint q).Hf (fun v => X v.1 v.2) := by
  have h := cHf_joint_ge p q X (fun _ _ => (0:ℕ))
  simpa only [cHf,Hf_const,sub_zero,Hf_pair_const_right] using h

end FinLaw

open scoped BigOperators Classical

noncomputable def SplitSieve.pointEntropy {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve) (P : FinLaw Ω) (Z : Ω → GaussianInt) (b : ℕ) : ℝ :=
  P.signedEntropy (fun σ ω => s.residueVector σ (Z ω)) b

noncomputable def SplitSieve.freshCoordinate {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve) (P : FinLaw Ω) (X Y : Ω → GaussianInt)
    (b : ℕ) (hb : b < s.primes.card) : ℝ :=
  𝔼 σ : Fin s.primes.card → Bool, 𝔼 π : Equiv.Perm (Fin s.primes.card),
    P.cHf (fun ω => s.residueVector σ (X ω-Y ω) (π ⟨b,hb⟩))
      (fun ω => (FinLaw.prefixVar (fun x => s.residueVector σ (X x)) π b ω,
        FinLaw.prefixVar (fun x => s.residueVector σ (Y x)) π b ω))

lemma SplitSieve.freshCoordinate_map {Ω : Type uOmega} {Κ : Type uCapitalKappa} [Fintype Ω] [Fintype Κ]
    (s : SplitSieve) (p : FinLaw Ω) (f : Ω → Κ) (X Y : Κ → GaussianInt)
    (b : ℕ) (hb : b < s.primes.card) :
    s.freshCoordinate (p.map f) X Y b hb = s.freshCoordinate p (X ∘ f) (Y ∘ f) b hb := by
  unfold SplitSieve.freshCoordinate
  simp only [FinLaw.cHf_map,Function.comp_def]
  rfl

noncomputable def differenceLaw (z : ℕ → GaussianInt) (n : ℕ) :
    FinLaw (Fin (n+1) × Fin (n+1)) := by
  let := (differences_walkSegment_nonempty z n).to_subtype
  exact (FinLaw.uniform (differences (walkSegment z n))).map (differenceRepresentative z n)

theorem differenceLaw_fresh (s : SplitSieve) (z : ℕ → GaussianInt) (n : ℕ)
    {b r : ℕ} (hbr : b < r) (hr : r ≤ s.primes.card)
    {T R W d δ : ℝ} {e : ℂ} (he : ‖e‖=1) (hT : 5 ≤ T)
    (hpT : ∀ p ∈ s.primes, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hd : 0 < d) (hd1 : d < 1/4)
    (hδ : 0 < δ) (hgap : Real.log (R*W) ≤ (1-d)*(r*s.meanLog-δ))
    (hlarge : 1000 ≤ d^3*r)
    (hΔ : ∀ x ∈ differences (walkSegment z n), ∀ y ∈ differences (walkSegment z n),
      x-y ∈ orientedRectangle e R W) :
    (1-r*(Real.log 2)^2/δ^2-Real.exp (-(d^3*r/5120)))*
        Real.log (differences (walkSegment z n)).card-2*b*Real.log (2*T) ≤
      (r-b : ℕ)*s.freshCoordinate (differenceLaw z n)
        (fun ij => z ij.1.val) (fun ij => z ij.2.val) b (by omega) := by
  let Δ := differences (walkSegment z n)
  let hne := differences_walkSegment_nonempty z n
  let := hne.to_subtype
  let X : Δ → GaussianInt := fun ω => z (differenceRepresentative z n ω).1.val
  let Y : Δ → GaussianInt := fun ω => z (differenceRepresentative z n ω).2.val
  have hXY : ∀ ω, X ω-Y ω=ω := differenceRepresentative_spec z n
  have h := s.actual_fresh_entropy hbr hr Δ hne X Y hXY he hT hpT hW hWR hd hd1 hδ hgap hlarge hΔ
  change _ ≤ (r-b : ℕ)*s.freshCoordinate
    ((FinLaw.uniform Δ).map (differenceRepresentative z n))
      (fun ij => z ij.1.val) (fun ij => z ij.2.val) b (by omega)
  rw [s.freshCoordinate_map]
  change _ ≤ (r-b : ℕ)*s.freshCoordinate (FinLaw.uniform Δ) X Y b (by omega)
  simpa only [SplitSieve.freshCoordinate,hXY] using h

theorem SplitSieve.freshCoordinate_joint_ge {ι : Type uIota} {Ω : Type uOmega} [Fintype ι] [Fintype Ω]
    (s : SplitSieve) (p : FinLaw ι) (q : ι → FinLaw Ω)
    (X Y : ι → Ω → GaussianInt) {b : ℕ} (hb : b < s.primes.card) :
    (∑ i, p i*s.freshCoordinate (q i) (X i) (Y i) b hb) ≤
      s.freshCoordinate (p.joint q) (fun v => X v.1 v.2) (fun v => Y v.1 v.2) b hb := by
  have h := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ =>
      p.cHf_joint_ge q (fun i ω => s.residueVector σ (X i ω-Y i ω) (π ⟨b,hb⟩))
        (fun i ω => (FinLaw.prefixVar (fun x => s.residueVector σ (X i x)) π b ω,
          FinLaw.prefixVar (fun x => s.residueVector σ (Y i x)) π b ω))))
  simpa only [SplitSieve.freshCoordinate,Finset.expect_sum_comm,Finset.mul_expect] using! h

lemma pointEntropy_fair_endpoint {Ω : Type uOmega} [Fintype Ω] (s : SplitSieve)
    (p : FinLaw Ω) (X Y : Ω → GaussianInt) (b : ℕ) :
    s.pointEntropy p X b+s.pointEntropy p Y b ≤
      2*s.pointEntropy ((FinLaw.uniform Bool).joint (fun _ => p))
        (fun v => if v.1 then X v.2 else Y v.2) b := by
  have h := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ =>
      (FinLaw.uniform Bool).Hf_joint_ge (fun _ => p)
        (fun c ω => FinLaw.prefixVar (fun x => s.residueVector σ (if c then X x else Y x)) π b ω)))
  simp only [Fintype.sum_bool,FinLaw.uniform_mass,Fintype.card_bool,Nat.cast_ofNat,
    Bool.false_eq_true,ite_false,ite_true,Finset.expect_add_distrib,← Finset.mul_expect] at h
  change (2:ℝ)⁻¹*s.pointEntropy p X b+(2:ℝ)⁻¹*s.pointEntropy p Y b ≤
    s.pointEntropy ((FinLaw.uniform Bool).joint (fun _ => p))
      (fun v => if v.1 then X v.2 else Y v.2) b at h
  linarith

theorem SplitSieve.point_enrichment_accounting {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve) (p : FinLaw Ω) (X Y Z : Ω → GaussianInt)
    {b q : ℕ} (hb : 0 < b) (hbq : b < q) (hq : q ≤ s.primes.card) :
    (b : ℝ)*((q-b : ℕ)*s.freshCoordinate p X Y b (by omega)+
      s.pointEntropy p Z q-p.Hf (fun ω => X ω-Y ω)-p.Hf (fun ω => X ω-Z ω)) ≤
      (q : ℝ)*(s.pointEntropy p X b+s.pointEntropy p Y b) := by
  have h (σ : Fin s.primes.card → Bool) := p.ordered_enrichment_accounting
    (fun ω => s.residueVector σ (X ω)) (fun ω => s.residueVector σ (Y ω))
    (fun ω => s.residueVector σ (Z ω)) (fun ω => s.residueVector σ (X ω-Y ω))
    (fun ω => X ω-Y ω) (fun ω => X ω-Z ω) hb hbq hq
    (by intro i ω ν hx hy; exact residueCode_sub hx hy)
    (by
      intro i ω ν hx hd
      have h := residueCode_sub hx hd
      simpa only [sub_sub_cancel,SplitSieve.residueVector] using h)
    (by intro i ω ν hh; rw [hh])
    (by
      intro i ω ν hx he
      have h := residueCode_sub hx (congrArg (residueCode _) he)
      simpa only [sub_sub_cancel,SplitSieve.residueVector] using h)
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun σ _ => h σ)
  simpa only [SplitSieve.pointEntropy,FinLaw.signedEntropy,SplitSieve.freshCoordinate,
    Finset.expect_sub_distrib,Finset.expect_add_distrib,← Finset.mul_expect,Fintype.expect_const] using hh

theorem SplitSieve.actual_enrichment {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve) (p : FinLaw Ω) (X Y Z : Ω → GaussianInt)
    {b q : ℕ} (hb : 0 < b) (hbq : b < q) (hq : q ≤ s.primes.card)
    {F R : ℝ} (hF : F ≤ s.freshCoordinate p X Y b (by omega))
    (hR : 1 ≤ R) (hXY : ∀ ω, ‖((X ω-Y ω:GaussianInt):ℂ)‖ ≤ R)
    (hXZ : ∀ ω, ‖((X ω-Z ω:GaussianInt):ℂ)‖ ≤ R) :
    (b : ℝ)*((q-b : ℕ)*F+s.pointEntropy p Z q-2*(Real.log 36+2*Real.log R)) ≤
      2*(q : ℝ)*s.pointEntropy ((FinLaw.uniform Bool).joint (fun _ => p))
        (fun v => if v.1 then X v.2 else Y v.2) b := by
  have hc := s.point_enrichment_accounting p X Y Z hb hbq hq
  have h1 := displacement_entropy_le p (fun ω => X ω-Y ω) hR hXY
  have h2 := displacement_entropy_le p (fun ω => X ω-Z ω) hR hXZ
  have he := pointEntropy_fair_endpoint s p X Y b
  have hm := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg q)
  have hf := mul_le_mul_of_nonneg_left hF (show (0:ℝ) ≤ (q-b:ℕ) by positivity)
  have hsub : (q-b:ℕ)*F+s.pointEntropy p Z q-2*(Real.log 36+2*Real.log R) ≤
      (q-b:ℕ)*s.freshCoordinate p X Y b (by omega)+s.pointEntropy p Z q-
        p.Hf (fun ω => X ω-Y ω)-p.Hf (fun ω => X ω-Z ω) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg b)
  linarith

open scoped BigOperators Classical

lemma fresh_error_bounds {g L r : ℝ} (hg : 0 < g) (hg1 : g ≤ 1/100)
    (hL : 1 ≤ L) (hr : 0 < r) (hlarge : 5120 ≤ g^4*r) :
    r*(Real.log 2)^2/(2*g*r*L)^2 ≤ g ∧ Real.exp (-(g^3*r/5120)) ≤ g := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hl2 : (Real.log 2)^2 ≤ 1 := by nlinarith
  have hg4 : 0 < g^4 := pow_pos hg _
  have hg3 : 0 < g^3 := pow_pos hg _
  have hgL : 0 < 2*g*r*L := by positivity
  have hgr : 1 ≤ g^3*r := by
    have h : g^4*r = g*(g^3*r) := by ring
    have hp : 0 ≤ g^3*r := mul_nonneg hg3.le hr.le
    nlinarith
  have hLL : 1 ≤ L^2 := by nlinarith
  have hprod := mul_le_mul hgr hLL (by norm_num : (0:ℝ)≤1) (mul_nonneg hg3.le hr.le)
  have hrr : 0 ≤ r*(4*(g^3*r*L^2)-1) := mul_nonneg hr.le (by linarith)
  constructor
  · apply (div_le_iff₀ (sq_pos_of_pos hgL)).mpr
    have h := mul_le_mul_of_nonneg_left hl2 hr.le
    linarith
  · have hpow : 1/g ≤ g^3*r/5120 := by
      apply (div_le_iff₀ hg).mpr
      linarith
    have hlogg : -(1/g) ≤ Real.log g := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hg)
      rw [Real.log_inv] at h
      simp only [one_div] at h ⊢
      linarith
    exact (Real.exp_le_exp.mpr (by linarith : -(g^3*r/5120) ≤ Real.log g)).trans_eq
      (Real.exp_log hg)

lemma fresh_gap_bound {g a L r : ℝ} (hg : 0 < g) (hg1 : g ≤ 1/100)
    (ha : 0 ≤ a) (hlow : (1+10*g)*a ≤ r*L) :
    a ≤ (1-g)*(r*L-2*g*r*L) := by
  have hfac : 0 ≤ (1-g)*(1-2*g) := mul_nonneg (by linarith) (by linarith)
  have h := mul_le_mul_of_nonneg_left hlow hfac
  have hn : 0 ≤ g*(7-30*g) := mul_nonneg hg.le (by linarith)
  have he : 1 ≤ (1-g)*(1-2*g)*(1+10*g) := by
    have hg3 : 0 ≤ g^3 := pow_nonneg hg.le _
    linarith
  have ha' := mul_le_mul_of_nonneg_right he ha
  linarith

theorem SplitSieve.differenceLaw_fresh_lower (s : SplitSieve)
    (z : ℕ → GaussianInt) (n : ℕ) {b r : ℕ}
    (hbr : b < r) (hr : r ≤ s.primes.card)
    {T R W g a : ℝ} {e : ℂ} (he : ‖e‖=1) (hT : 5 ≤ T)
    (hpT : ∀ p ∈ s.primes, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hg : 0 < g) (hg1 : g ≤ 1/100)
    (hmean : 1 ≤ s.meanLog) (ha : a = Real.log (R*W)) (ha0 : 0 ≤ a)
    (hlow : (1+10*g)*a ≤ r*s.meanLog) (hhigh : r*s.meanLog ≤ (1+11*g)*a)
    (hlarge : 5120 ≤ g^4*r)
    (hsize : (1-g)*a ≤ Real.log (differences (walkSegment z n)).card)
    (hcost : 2*b*Real.log (2*T) ≤ 8*g*a)
    (hΔ : ∀ x ∈ differences (walkSegment z n), ∀ y ∈ differences (walkSegment z n),
      x-y ∈ orientedRectangle e R W) :
    (1-30*g)*s.meanLog ≤ s.freshCoordinate (differenceLaw z n)
      (fun ij => z ij.1.val) (fun ij => z ij.2.val) b (by omega) := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hg14 : g < 1/4 := by linarith
  have hδ : 0 < 2*g*r*s.meanLog := by positivity
  have hgap : Real.log (R*W) ≤ (1-g)*(r*s.meanLog-2*g*r*s.meanLog) := by
    rw [← ha]
    exact fresh_gap_bound hg hg1 ha0 hlow
  have hlarge' : 1000 ≤ g^3*(r:ℝ) := by
    have hp : 0 ≤ g^3*(r:ℝ) := by positivity
    have hid : g^4*(r:ℝ) = g*(g^3*r) := by ring
    nlinarith
  have herr := fresh_error_bounds hg hg1 hmean hr0 hlarge
  have h := differenceLaw_fresh s z n hbr hr he hT hpT hW hWR hg hg14 hδ
    hgap hlarge' hΔ
  have hsize0 : 0 ≤ Real.log (differences (walkSegment z n)).card := by
    have hh : 0 ≤ (1-g)*a := mul_nonneg (by linarith) ha0
    linarith
  have he := mul_le_mul_of_nonneg_right (show 1-2*g ≤
      1-(r:ℝ)*(Real.log 2)^2/(2*g*r*s.meanLog)^2-
        Real.exp (-(g^3*r/5120)) by linarith [herr.1,herr.2]) hsize0
  have hs := mul_le_mul_of_nonneg_left hsize (show 0 ≤ 1-2*g by linarith)
  have hnum : (1-11*g)*a ≤ (r-b:ℕ)*s.freshCoordinate (differenceLaw z n)
      (fun ij => z ij.1.val) (fun ij => z ij.2.val) b (by omega) := by
    have hx : 0 ≤ 2*g^2*a := by positivity
    linarith
  have hp0 : 0 ≤ 1-30*g := by linarith
  have hh := mul_le_mul_of_nonneg_left hhigh hp0
  have hh2 : (1-30*g)*((1+11*g)*a) ≤ (1-11*g)*a := by
    have h1 : 0 ≤ g*a := mul_nonneg hg.le ha0
    have h2 : 0 ≤ g^2*a := mul_nonneg (sq_nonneg _) ha0
    linarith
  have hbrR : (r-b:ℕ) ≤ (r:ℝ) := by exact_mod_cast Nat.sub_le r b
  have hb0 : (0:ℝ) < (r-b:ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hbr
  have hm := mul_le_mul_of_nonneg_right hbrR (mul_nonneg hp0 (by linarith : 0 ≤ s.meanLog))
  have key : ((r-b:ℕ):ℝ)*((1-30*g)*s.meanLog) ≤ ((r-b:ℕ):ℝ)*s.freshCoordinate (differenceLaw z n)
      (fun ij => z ij.1.val) (fun ij => z ij.2.val) b (by omega) := by linarith
  exact le_of_mul_le_mul_left key hb0

lemma SplitSieve.meanLog_bounds (s : SplitSieve) (hne : s.primes.Nonempty) {T : ℝ}
    (hT : 0 < T) (hpT : ∀ p ∈ s.primes, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T) :
    Real.log T ≤ s.meanLog ∧ s.meanLog ≤ Real.log (2*T) := by
  have : Nonempty (Fin s.primes.card) := Fin.pos_iff_nonempty.mp (Finset.card_pos.mpr hne)
  constructor
  · have h := Finset.expect_le_expect (s := Finset.univ) (fun i _ =>
      Real.log_le_log hT (hpT _ (s.enumeration i).property).1)
    simpa only [SplitSieve.meanLog,Fintype.expect_const] using h
  · apply Finset.expect_le (Finset.univ_nonempty)
    intro i _
    exact Real.log_le_log (lt_of_lt_of_le hT (hpT _ (s.enumeration i).property).1)
      (hpT _ (s.enumeration i).property).2

theorem SplitSieve.walk_fresh_lower (s : SplitSieve) (hne : s.primes.Nonempty)
    (z : ℕ → GaussianInt) {n : ℕ} (hn : 1 ≤ n) (hinj : Function.Injective z)
    {D T g : ℝ} (hD : 1 ≤ D) (hT : 5 ≤ T)
    (hz : ∀ i < n, dist (z i:ℂ) (z (i+1):ℂ) ≤ D)
    (hpT : ∀ p ∈ s.primes, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hg : 0 < g) (hg1 : g ≤ 1/100) (hL : 1 ≤ s.meanLog)
    {b : ℕ} (hu : 0 < Real.log n-Real.log 18)
    (hround : s.meanLog ≤ g*(Real.log n-Real.log 18))
    (hlarge : 5120*s.meanLog ≤ g^4*(Real.log n-Real.log 18))
    (hcost : (b:ℝ)*s.meanLog ≤ g*(Real.log n-Real.log 18))
    (hsize : Real.log 16+Real.log (max D ((latticeBall (4*D)).card:ℝ)) ≤
      g*(Real.log n-Real.log 18))
    (hcap : 2*(2*Real.log n+Real.log 16+2*Real.log D) ≤ s.primes.card*s.meanLog) :
    ∃ hb : b < s.primes.card,
      (1-30*g)*s.meanLog ≤ s.freshCoordinate (differenceLaw z n)
        (fun ij => z ij.1.val) (fun ij => z ij.2.val) b hb := by
  obtain ⟨R,W,e,c,hW,hWR,he,hrect,hnA,hAup,hAΔ⟩ :=
    walk_many_differences z hn hinj hD hz
  have hRp : 0 < R := by linarith
  have hWp : 0 < W := by linarith
  have hA : 0 < R*W := mul_pos hRp hWp
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hLp : 0 < s.meanLog := by linarith
  let a := Real.log (16*(R*W))
  let u := Real.log n-Real.log 18
  have hua : u ≤ a := by
    have h := Real.log_le_log hnR hnA
    rw [Real.log_mul (by norm_num : (18:ℝ)≠0) hA.ne'] at h
    have hl16 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
    dsimp [u,a]
    rw [Real.log_mul (by norm_num : (16:ℝ)≠0) hA.ne']
    linarith
  have ha0 : 0 < a := lt_of_lt_of_le hu hua
  have hav : a ≤ 2*Real.log n+Real.log 16+2*Real.log D := by
    have h := Real.log_le_log hA hAup
    rw [Real.log_mul (pow_ne_zero _ (by linarith : D≠0)) (pow_ne_zero _ hnR.ne'),
      Real.log_pow,Real.log_pow] at h
    dsimp [a]
    rw [Real.log_mul (by norm_num : (16:ℝ)≠0) hA.ne']
    norm_num at h
    linarith only [h]
  let r := ⌈(1+10*g)*a/s.meanLog⌉₊
  have hlo : (1+10*g)*a ≤ (r:ℝ)*s.meanLog := by
    exact (div_le_iff₀ hLp).mp (Nat.le_ceil _)
  have hhi : (r:ℝ)*s.meanLog ≤ (1+11*g)*a := by
    have hx : 0 ≤ (1+10*g)*a/s.meanLog := by positivity
    have hc := Nat.ceil_lt_add_one hx
    have hh := mul_lt_mul_of_pos_right hc hLp
    have heq : ((1+10*g)*a/s.meanLog+1)*s.meanLog = (1+10*g)*a+s.meanLog := by
      rw [add_mul,div_mul_cancel₀ _ hLp.ne',one_mul]
    rw [heq] at hh
    have hgu := mul_le_mul_of_nonneg_left hua hg.le
    change (r:ℝ)*s.meanLog < (1+10*g)*a+s.meanLog at hh
    linarith only [hh,hround,hgu]
  have hr : r ≤ s.primes.card := by
    suffices hh : (r:ℝ) ≤ s.primes.card by exact_mod_cast hh
    have hh : (1+11*g)*a ≤ 2*a := by nlinarith only [hg1,ha0]
    nlinarith only [hhi,hh,hav,hcap,hLp]
  have hbr : b < r := by
    suffices hh : (b:ℝ) < r by exact_mod_cast hh
    have hgu := mul_le_mul_of_nonneg_left hua hg.le
    nlinarith only [hcost,hgu,hlo,hg1,hLp,ha0]
  have hlr : 5120 ≤ g^4*(r:ℝ) := by
    have hg4 : 0 < g^4 := pow_pos hg _
    have h1 : u ≤ (r:ℝ)*s.meanLog := by nlinarith only [hlo,hua,hg,ha0]
    have h2 := mul_le_mul_of_nonneg_left h1 hg4.le
    nlinarith only [h2,hlarge,hLp]
  have hC : 0 < max D ((latticeBall (4*D)).card:ℝ) := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hdc : (0:ℝ) < (differences (walkSegment z n)).card := by
    exact_mod_cast Finset.card_pos.mpr (differences_walkSegment_nonempty z n)
  have hsz : (1-g)*a ≤ Real.log (differences (walkSegment z n)).card := by
    have h := Real.log_le_log hA hAΔ
    rw [Real.log_mul hC.ne' hdc.ne'] at h
    have hgu := mul_le_mul_of_nonneg_left hua hg.le
    have haeq : a = Real.log 16+Real.log (R*W) := by
      exact Real.log_mul (by norm_num) hA.ne'
    linarith only [h,hgu,haeq,hsize]
  have hlog2 : Real.log (2*T) ≤ 2*s.meanLog := by
    have hm := s.meanLog_bounds hne (by linarith) hpT
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      linarith
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (by linarith : T≠0)]
    linarith only [hm.1,hlog2,hL]
  have hbc : 2*(b:ℝ)*Real.log (2*T) ≤ 8*g*a := by
    have h := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0:ℝ)≤2*b)
    have hgu := mul_le_mul_of_nonneg_left hua hg.le
    have hga : 0 ≤ g*a := by positivity
    linarith only [h,hgu,hcost,hga]
  refine ⟨by omega,?_⟩
  apply s.differenceLaw_fresh_lower z n hbr hr (e := star e) (R := 4*R) (W := 4*W)
    (by simpa using he) hT hpT (by linarith) (by linarith) hg hg1 hL
    (a := a) (by dsimp [a]; congr 1; ring) ha0.le hlo hhi hlr hsz hbc
  exact differences_rectangle (walkSegment z n) hrect

end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat

section
open scoped BigOperators Classical

structure TimeLaw where
  last : ℕ
  law : FinLaw (Fin (last+1))

noncomputable def endpointTime (a n : ℕ) :
    Bool × (Fin (a+1) × (Fin (n+1) × Fin (n+1))) → Fin (a+n+1) :=
  fun v => ⟨v.2.1.val+(if v.1 then v.2.2.1.val else v.2.2.2.val),by
    split_ifs <;> omega⟩

noncomputable def TimeLaw.step (P : TimeLaw) (z : ℕ → GaussianInt) (n : ℕ) : TimeLaw where
  last := P.last+n
  law := ((FinLaw.uniform Bool).joint (fun _ => P.law.joint (fun a =>
    differenceLaw (fun t => z (a.val+t)) n))).map (endpointTime P.last n)

lemma SplitSieve.pointEntropy_map {Ω : Type uOmega} {Κ : Type uCapitalKappa} [Fintype Ω] [Fintype Κ]
    (s : SplitSieve) (p : FinLaw Ω) (f : Ω → Κ) (Z : Κ → GaussianInt) (b : ℕ) :
    s.pointEntropy (p.map f) Z b = s.pointEntropy p (Z ∘ f) b := by
  unfold pointEntropy FinLaw.signedEntropy FinLaw.orderedEntropy
  simp only [FinLaw.Hf_map]
  rfl

lemma SplitSieve.pointEntropy_joint_fst {Ω : Type uOmega} {Κ : Type uCapitalKappa} [Fintype Ω] [Fintype Κ]
    (s : SplitSieve) (p : FinLaw Ω) (q : Ω → FinLaw Κ) (Z : Ω → GaussianInt) (b : ℕ) :
    s.pointEntropy (p.joint q) (fun v => Z v.1) b = s.pointEntropy p Z b := by
  have h := s.pointEntropy_map (p.joint q) Prod.fst Z b
  rw [FinLaw.joint_map_fst] at h
  exact h.symm

lemma shifted_walk_injective (z : ℕ → GaussianInt) (hz : Function.Injective z) (a : ℕ) :
    Function.Injective (fun t => z (a+t)) := by intro i j h; have := hz h; omega

lemma walk_pair_displacement (z : ℕ → GaussianInt) {D : ℝ} (hD : 0 ≤ D)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) (a n i j : ℕ)
    (hi : i ≤ n) (hj : j ≤ n) :
    ‖((z (a+i)-z (a+j):GaussianInt):ℂ)‖ ≤ D*n := by
  have h := walkSegment_dist_le (fun t => z (a+t)) hD
    (fun t _ => by simpa only [Nat.add_assoc] using hstep (a+t)) hi hj
  simpa only [dist_eq_norm,map_sub] using h

theorem TimeLaw.step_enrichment (P : TimeLaw) (s : SplitSieve)
    (z : ℕ → GaussianInt) {D F : ℝ} (hD : 1 ≤ D)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) {n b q : ℕ}
    (hn : 1 ≤ n) (hb : 0 < b) (hbq : b < q) (hq : q ≤ s.primes.card)
    (hF : ∀ a : Fin (P.last+1), F ≤ s.freshCoordinate
      (differenceLaw (fun t => z (a.val+t)) n)
      (fun ij => z (a.val+ij.1.val)) (fun ij => z (a.val+ij.2.val)) b (by omega)) :
    (b:ℝ)*((q-b:ℕ)*F+s.pointEntropy P.law (fun a => z a.val) q-
      2*(Real.log 36+2*Real.log (D*n))) ≤
      2*(q:ℝ)*s.pointEntropy (P.step z n).law (fun a => z a.val) b := by
  let K := P.law.joint (fun a => differenceLaw (fun t => z (a.val+t)) n)
  let X := fun v : Fin (P.last+1) × (Fin (n+1) × Fin (n+1)) => z (v.1.val+v.2.1.val)
  let Y := fun v : Fin (P.last+1) × (Fin (n+1) × Fin (n+1)) => z (v.1.val+v.2.2.val)
  let Z := fun v : Fin (P.last+1) × (Fin (n+1) × Fin (n+1)) => z v.1.val
  have hF' : F ≤ s.freshCoordinate K X Y b (by omega) := by
    have hh := s.freshCoordinate_joint_ge P.law
      (fun a => differenceLaw (fun t => z (a.val+t)) n)
      (fun a ij => z (a.val+ij.1.val)) (fun a ij => z (a.val+ij.2.val)) (by omega : b < s.primes.card)
    apply le_trans _ hh
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
      mul_le_mul_of_nonneg_left (hF a) (P.law.nonneg a))
    simpa only [← Finset.sum_mul,P.law.sum_one,one_mul] using hsum
  have hDn : 1 ≤ D*n := one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast hn)
  have h := s.actual_enrichment K X Y Z hb hbq hq hF' hDn
    (fun v => walk_pair_displacement z (by linarith) hstep _ _ _ _ (by omega) (by omega))
    (fun v => by
      change ‖((z (v.1.val+v.2.1.val)-z v.1.val:GaussianInt):ℂ)‖ ≤ D*n
      simpa only [Nat.add_zero] using
        walk_pair_displacement z (by linarith) hstep v.1.val n v.2.1.val 0 (by omega) (by omega))
  have hZ := s.pointEntropy_joint_fst P.law
    (fun a => differenceLaw (fun t => z (a.val+t)) n) (fun a => z a.val) q
  rw [hZ] at h
  have hout : s.pointEntropy (P.step z n).law (fun a => z a.val) b =
      s.pointEntropy ((FinLaw.uniform Bool).joint (fun _ => K))
        (fun v => if v.1 then X v.2 else Y v.2) b := by
    change s.pointEntropy (((FinLaw.uniform Bool).joint (fun _ => K)).map
      (endpointTime P.last n)) (fun a => z a.val) b = _
    rw [s.pointEntropy_map]
    apply congrArg (fun F => s.pointEntropy ((FinLaw.uniform Bool).joint (fun _ => K)) F b)
    funext v
    simp only [Function.comp_def,endpointTime,X,Y]
    split_ifs <;> rfl
  rw [hout]
  exact h

end

namespace FinLaw

section
open scoped BigOperators Classical
variable {Ω : Type uOmega} [Fintype Ω]

noncomputable def prob (p : FinLaw Ω) (E : Ω → Prop) : ℝ := ∑ ω, if E ω then p ω else 0

lemma prob_nonneg (p : FinLaw Ω) (E : Ω → Prop) : 0 ≤ p.prob E := by
  exact Finset.sum_nonneg (fun ω _ => by split_ifs <;> simp [p.nonneg ω])

lemma prob_le_one (p : FinLaw Ω) (E : Ω → Prop) : p.prob E ≤ 1 := by
  rw [← p.sum_one]
  exact Finset.sum_le_sum (fun ω _ => by split_ifs <;> simp [p.nonneg ω])

lemma prob_mono (p : FinLaw Ω) {E F : Ω → Prop} (h : ∀ ω, E ω → F ω) :
    p.prob E ≤ p.prob F := by
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : E ω
  · simp [he,h ω he]
  · by_cases hf : F ω <;> simp [he,hf,p.nonneg ω]

noncomputable def iid (p : FinLaw Ω) (n : ℕ) : FinLaw (Fin n → Ω) where
  mass := fun x => ∏ i, p (x i)
  nonneg := fun x => Finset.prod_nonneg (fun i _ => p.nonneg _)
  sum_one := by
    rw [← Fintype.prod_sum]
    simp only [p.sum_one,Finset.prod_const_one]

@[simp] lemma iid_mass (p : FinLaw Ω) (n : ℕ) (x : Fin n → Ω) :
    p.iid n x = ∏ i, p (x i) := rfl

lemma iid_product (p : FinLaw Ω) (n : ℕ) (f : Ω → ℝ) :
    (∑ x : Fin n → Ω, p.iid n x * ∏ i, f (x i)) = (∑ ω, p ω*f ω)^n := by
  simp only [iid_mass,← Finset.prod_mul_distrib]
  exact (Fintype.sum_pow (fun ω => p ω*f ω) n).symm

lemma exp_neg_le_quadratic {t : ℝ} (ht : 0 ≤ t) : Real.exp (-t) ≤ 1-t+t^2/2 := by
  have hm : Monotone (fun x : ℝ => 1-x+x^2/2-Real.exp (-x)) := by
    apply monotone_of_hasDerivAt_nonneg (f' := fun x => -1+x+Real.exp (-x))
    · intro x
      convert! (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).add
        (((hasDerivAt_id x).pow 2).div_const 2)).sub
          (((hasDerivAt_id x).neg).exp) using 1
      simp only [Pi.neg_apply,id_eq]
      ring
    · intro x
      have h := Real.add_one_le_exp (-x)
      change 0 ≤ -1+x+Real.exp (-x)
      linarith
  have h := hm ht
  simpa using h

lemma prob_le_exp_moment (p : FinLaw Ω) (S : Ω → ℝ) {t a : ℝ} (ht : 0 ≤ t) :
    p.prob (fun ω => S ω ≤ a) ≤ Real.exp (t*a) * ∑ ω, p ω*Real.exp (-t*S ω) := by
  have h (ω : Ω) : (if S ω ≤ a then p ω else 0) ≤
      Real.exp (t*a)*(p ω*Real.exp (-t*S ω)) := by
    by_cases hh : S ω ≤ a
    · rw [ite_eq_left hh]
      have he : 1 ≤ Real.exp (t*a+-t*S ω) := Real.one_le_exp_iff.mpr (by nlinarith)
      calc
        p ω = p ω*1 := by ring
        _ ≤ p ω*Real.exp (t*a+-t*S ω) := mul_le_mul_of_nonneg_left he (p.nonneg ω)
        _ = Real.exp (t*a)*(p ω*Real.exp (-t*S ω)) := by rw [Real.exp_add]; ring
    · rw [ite_eq_right hh]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (p.nonneg ω) (Real.exp_pos _).le)
  simpa only [prob,Finset.mul_sum] using Finset.sum_le_sum (s := Finset.univ) (fun ω _ => h ω)

lemma bernoulli_moment (p : FinLaw Ω) (E : Ω → Prop) (t : ℝ) :
    (∑ ω, p ω*Real.exp (-t*(if E ω then 1 else 0))) =
      1+p.prob E*(Real.exp (-t)-1) := by
  have he (ω : Ω) : p ω*Real.exp (-t*(if E ω then 1 else 0)) =
      p ω+(if E ω then p ω else 0)*(Real.exp (-t)-1) := by
    split_ifs <;> simp only [mul_one,mul_zero,Real.exp_zero,zero_mul,add_zero]
    ring
  simp only [he,Finset.sum_add_distrib,← Finset.sum_mul,p.sum_one,prob]

theorem iid_lower_tail (p : FinLaw Ω) (E : Ω → Prop) (n : ℕ)
    {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 ≤ δ) (hp : μ ≤ p.prob E) :
    (p.iid n).prob (fun x => (∑ i : Fin n, if E (x i) then (1:ℝ) else 0) ≤ n*(μ-δ)) ≤
      Real.exp (- (n:ℝ)*δ^2/(2*μ)) := by
  let t := δ/μ
  have ht : 0 ≤ t := div_nonneg hδ hμ.le
  have hm := prob_le_exp_moment (p.iid n)
    (fun x => ∑ i : Fin n, if E (x i) then (1:ℝ) else 0) ht (a := n*(μ-δ))
  have hfactor : (∑ x : Fin n → Ω, p.iid n x *
      Real.exp (-t*∑ i : Fin n, if E (x i) then 1 else 0)) =
      (1+p.prob E*(Real.exp (-t)-1))^n := by
    simp_rw [Finset.mul_sum,Real.exp_sum]
    rw [iid_product p n (fun ω => Real.exp (-t*(if E ω then 1 else 0))),bernoulli_moment]
  rw [hfactor] at hm
  have hbase0 : 0 ≤ 1+p.prob E*(Real.exp (-t)-1) := by
    rw [← bernoulli_moment]
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg (p.nonneg ω) (Real.exp_pos _).le)
  have hbase : 1+p.prob E*(Real.exp (-t)-1) ≤ Real.exp (μ*(Real.exp (-t)-1)) := by
    have hn : Real.exp (-t)-1 ≤ 0 := by
      have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
      linarith
    have h1 := mul_le_mul_of_nonpos_right hp hn
    have h2 := Real.add_one_le_exp (μ*(Real.exp (-t)-1))
    linarith
  have hpw := pow_le_pow_left₀ hbase0 hbase n
  have hmul := mul_le_mul_of_nonneg_left hpw (Real.exp_pos (t*(n*(μ-δ)))).le
  apply hm.trans (hmul.trans ?_)
  rw [← Real.exp_nat_mul,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he := exp_neg_le_quadratic ht
  have h := mul_le_mul_of_nonneg_left he (mul_nonneg (Nat.cast_nonneg n) hμ.le)
  have hid : t*((n:ℝ)*(μ-δ))+(n:ℝ)*μ*(-t+t^2/2) = -(n:ℝ)*δ^2/(2*μ) := by
    dsimp [t]
    field_simp
    ring
  rw [← hid]
  linarith

end

section
open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]

lemma le_map_apply (p : FinLaw Ω) (X : Ω → α) (ω : Ω) : p ω ≤ p.map X (X ω) := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun ν => if X ν=X ω then p ν else 0)
    (fun ν _ => by split_ifs <;> simp [p.nonneg ν]) (Finset.mem_univ ω)
  simpa only [ite_true,map_mass] using h

noncomputable def conditionOn (p : FinLaw Ω) (X : Ω → α) (a : α) : FinLaw Ω :=
  if h : p.map X a = 0 then p else {
    mass := fun ω => if X ω=a then p ω/(p.map X a) else 0
    nonneg := fun ω => by split_ifs; exact div_nonneg (p.nonneg ω) ((p.map X).nonneg a); rfl
    sum_one := by
      have he : (∑ ω, if X ω=a then p ω/(p.map X a) else 0) =
          (∑ ω, if X ω=a then p ω else 0)/(p.map X a) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro ω _
        split_ifs <;> simp
      rw [he,← map_mass,div_self h] }

lemma conditionOn_weight (p : FinLaw Ω) (X : Ω → α) (a : α) (ω : Ω) :
    p.map X a * p.conditionOn X a ω = if X ω=a then p ω else 0 := by
  by_cases hz : p.map X a=0
  · rw [hz,zero_mul]
    split_ifs with hh
    · have h := p.le_map_apply X ω
      rw [hh,hz] at h
      exact (le_antisymm h (p.nonneg ω)).symm
    · rfl
  · unfold conditionOn
    rw [dite_eq_right hz]
    change p.map X a * (if X ω=a then p ω/(p.map X a) else 0) = _
    by_cases hx : X ω=a
    · rw [ite_eq_left hx,ite_eq_left hx]
      exact mul_div_cancel₀ _ hz
    · rw [ite_eq_right hx,ite_eq_right hx,mul_zero]

lemma disintegration (p : FinLaw Ω) (X : Ω → α) :
    (p.map X).joint (p.conditionOn X) = p.map (fun ω => (X ω,ω)) := by
  ext ⟨a,ω⟩
  rw [joint_mass,conditionOn_weight,map_mass]
  simp only [Prod.mk.injEq]
  rw [Finset.sum_eq_single ω]
  · simp
  · intro ν _ hn
    simp [hn]
  · simp

lemma conditionOn_mixture (p : FinLaw Ω) (X : Ω → α) :
    (p.map X).mix (p.conditionOn X) = p := by
  rw [← joint_map_snd,disintegration,map_comp]
  exact p.map_id

lemma conditionOn_observation (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.H (fun ω => (X ω,Y ω)) = p.H X+∑ a, p.map X a*(p.conditionOn X a).H Y := by
  have h := (p.map X).Hf_joint_pair (p.conditionOn X) Y
  rw [disintegration,Hf_map] at h
  simpa only [Hf_eq_H,H,Function.comp_def] using h

lemma condH_eq_conditionOn (p : FinLaw Ω) (Y : Ω → β) (X : Ω → α) :
    p.condH Y X = ∑ a, p.map X a*(p.conditionOn X a).H Y := by
  unfold condH
  rw [p.H_pair_comm Y X,p.conditionOn_observation X Y]
  ring

lemma prob_map (p : FinLaw Ω) (f : Ω → α) (E : α → Prop) :
    (p.map f).prob E = p.prob (fun ω => E (f ω)) := by
  simp only [prob,map_mass]
  have h (a : α) : (if E a then ∑ ω, if f ω=a then p ω else 0 else 0) =
      ∑ ω, if f ω=a then (if E a then p ω else 0) else 0 := by
    by_cases he : E a <;> simp [he]
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp

lemma prob_joint (p : FinLaw Ω) (q : Ω → FinLaw α) (E : Ω × α → Prop) :
    (p.joint q).prob E = ∑ ω, p ω*(q ω).prob (fun a => E (ω,a)) := by
  simp only [prob,Fintype.sum_prod_type,joint_mass,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

lemma conditionOn_prob (p : FinLaw Ω) (X : Ω → α) (E : Ω → Prop) :
    (∑ a, p.map X a*(p.conditionOn X a).prob E) = p.prob E := by
  rw [← prob_joint (p.map X) (p.conditionOn X) (fun v => E v.2),disintegration,prob_map]

lemma prob_le_expect_div (p : FinLaw Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω)
    {a : ℝ} (ha : 0 < a) :
    p.prob (fun ω => a < f ω) ≤ (∑ ω, p ω*f ω)/a := by
  apply (le_div_iff₀ ha).mpr
  rw [prob,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hh : a < f ω
  · simp only [ite_eq_left hh]
    exact mul_le_mul_of_nonneg_left hh.le (p.nonneg ω)
  · simp only [ite_eq_right hh,zero_mul]
    exact mul_nonneg (p.nonneg ω) (hf ω)

lemma prob_compl (p : FinLaw Ω) (E : Ω → Prop) :
    p.prob (fun ω => ¬ E ω) = 1-p.prob E := by
  have h : p.prob (fun ω => ¬ E ω)+p.prob E = 1 := by
    rw [prob,prob,← Finset.sum_add_distrib,← p.sum_one]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases he : E ω <;> simp [he]
  linarith

lemma prob_inter_ge (p : FinLaw Ω) (E F : Ω → Prop) :
    p.prob E-p.prob (fun ω => ¬ F ω) ≤ p.prob (fun ω => E ω ∧ F ω) := by
  rw [prob,prob,prob,← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases he : E ω <;> by_cases hf : F ω <;> simp [he,hf,p.nonneg ω]

lemma prob_exists_le_sum {ι : Type uIota} [Fintype ι] (p : FinLaw Ω) (E : ι → Ω → Prop) :
    p.prob (fun ω => ∃ i, E i ω) ≤ ∑ i, p.prob (E i) := by
  simp only [prob]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hh : ∃ i, E i ω
  · obtain ⟨i,hi⟩ := hh
    rw [ite_eq_left ⟨i,hi⟩]
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun i => if E i ω then p ω else 0)
      (fun j _ => by split_ifs <;> simp [p.nonneg ω]) (Finset.mem_univ i)
    simpa only [ite_eq_left hi] using h
  · simp only [ite_eq_right hh]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> simp [p.nonneg ω])

end

open scoped BigOperators Classical
variable {Ω : Type uOmega} {Κ : Type uCapitalKappa} {ι : Type uIota} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω] [Fintype Κ] [Fintype ι]

lemma map_equiv_mass (p : FinLaw Ω) (e : Ω ≃ Κ) (x : Κ) :
    p.map e x = p (e.symm x) := by
  rw [map_mass,Finset.sum_eq_single (e.symm x)]
  · simp
  · intro ω _ hn
    have hh : e ω ≠ x := by intro h; exact hn (e.injective (by simpa using h))
    simp [hh]
  · simp

lemma entropy_map_equiv (p : FinLaw Ω) (e : Ω ≃ Κ) :
    (p.map e).entropy = p.entropy := by
  simp only [entropy,entropySum,map_equiv_mass]
  exact e.symm.sum_comp (fun ω => Real.negMulLog (p ω))

lemma iid_succ (p : FinLaw Ω) (n : ℕ) :
    p.iid (n+1) = (p.joint (fun _ => p.iid n)).map
      (Fin.consEquiv (fun _ : Fin (n+1) => Ω)) := by
  ext x
  rw [map_equiv_mass]
  change (∏ i : Fin (n+1), p (x i)) = p (x 0)*(∏ i : Fin n, p (x i.succ))
  exact Fin.prod_univ_succ _

lemma entropy_iid (p : FinLaw Ω) (n : ℕ) :
    (p.iid n).entropy = n*p.entropy := by
  induction n with
  | zero =>
    have he : p.iid 0 = uniform (Fin 0 → Ω) := by ext x; simp [uniform_mass]
    rw [he]
    simp [entropy,entropySum,uniform_mass]
  | succ n ih =>
    rw [iid_succ,entropy_map_equiv,entropy_joint]
    simp only [ih,← Finset.sum_mul,p.sum_one,one_mul,Nat.cast_add,Nat.cast_one]
    ring

lemma iid_split (p : FinLaw Ω) (n : ℕ) (i : Fin n) :
    p.iid n = (p.joint (fun _ =>
      ({ mass := fun x : (j : {j : Fin n // j ≠ i}) → Ω => ∏ j, p (x j)
         nonneg := fun x => Finset.prod_nonneg (fun j _ => p.nonneg _)
         sum_one := by rw [← Fintype.prod_sum]; simp only [p.sum_one,Finset.prod_const_one] } :
            FinLaw ((j : {j : Fin n // j ≠ i}) → Ω)))).map
      (Equiv.piSplitAt i (fun _ : Fin n => Ω)).symm := by
  ext x
  rw [map_equiv_mass]
  change (∏ j : Fin n, p (x j)) = p (x i)*(∏ j : {j : Fin n // j ≠ i}, p (x j))
  rw [← Fintype.prod_subtype_mul_prod_subtype (p := fun j : Fin n => j=i)]
  have he : (∏ j : {j : Fin n // j=i}, p (x j)) = p (x i) := by
    have hsub := Finset.prod_subtype (F := inferInstance) (p := fun j : Fin n => j=i) ({i} : Finset (Fin n)) (by simp) (fun j => p (x j))
    simpa using hsub.symm
  convert! congrArg (fun v => v*(∏ j : {j : Fin n // j ≠ i}, p (x j))) he using 1
  congr 1
  congr 1
  ext j
  simp only [Finset.mem_univ]

lemma iid_map_eval (p : FinLaw Ω) (n : ℕ) (i : Fin n) :
    (p.iid n).map (fun x => x i) = p := by
  rw [iid_split p n i,map_comp]
  have he : ((fun x : Fin n → Ω => x i) ∘ (Equiv.piSplitAt i (fun _ : Fin n => Ω)).symm) = Prod.fst := by
    funext x
    simp [Equiv.piSplitAt]
  rw [he,joint_map_fst]

end FinLaw
end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat

section
open scoped BigOperators Classical

namespace FinLaw
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]

lemma mix_map_left (p : FinLaw Ω) (f : Ω → α) (q : α → FinLaw β) :
    (p.map f).mix q = p.mix (fun ω => q (f ω)) := by
  ext b
  simp only [mix_mass,map_mass,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [ite_mul,zero_mul]
  rw [Finset.sum_ite_eq]
  simp

lemma mix_assoc (p : FinLaw Ω) (q : Ω → FinLaw α) (r : α → FinLaw β) :
    (p.mix q).mix r = p.mix (fun ω => (q ω).mix r) := by
  ext b
  simp only [mix_mass,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma joint_observation (p : FinLaw Ω) (q : Ω → FinLaw α) (F : Ω → α → β) :
    (p.joint q).map (fun v => F v.1 v.2) = p.mix (fun ω => (q ω).map (F ω)) := by
  have h := congrArg (fun r : FinLaw (Ω × β) => r.map Prod.snd) (joint_map_fiber p q F)
  simpa only [map_comp,joint_map_snd,Function.comp_def] using h

lemma joint_associate (p : FinLaw Ω) (q : Ω → FinLaw α) (r : Ω → α → FinLaw β) :
    ((p.joint q).joint (fun v => r v.1 v.2)).map (fun v => (v.1.1,(v.1.2,v.2))) =
      p.joint (fun ω => (q ω).joint (r ω)) := by
  ext v
  rcases v with ⟨ω,a,b⟩
  change ((p.joint q).joint (fun v => r v.1 v.2)).map (Equiv.prodAssoc Ω α β) (ω,a,b) = _
  rw [map_equiv_mass]
  simp only [Equiv.prodAssoc_symm_apply,joint_mass,mul_assoc]

end FinLaw

structure ForwardKernel where
  bound : ℕ
  law : ℕ → FinLaw (Fin (bound+1))

noncomputable def addOffsets (n m : ℕ) : Fin (n+1) × Fin (m+1) → Fin (n+m+1) :=
  fun v => ⟨v.1.val+v.2.val,by omega⟩

noncomputable def ForwardKernel.then (K R : ForwardKernel) : ForwardKernel where
  bound := K.bound+R.bound
  law := fun a => ((K.law a).joint (fun i => R.law (a+i.val))).map
    (addOffsets K.bound R.bound)

noncomputable def differenceKernel (z : ℕ → GaussianInt) (n : ℕ) : ForwardKernel where
  bound := n
  law := fun a => ((FinLaw.uniform Bool).joint (fun _ =>
    differenceLaw (fun t => z (a+t)) n)).map (fun v => if v.1 then v.2.1 else v.2.2)

noncomputable def smoothingKernel (n : ℕ) : ForwardKernel where
  bound := n
  law := fun _ => FinLaw.uniform (Fin (n+1))

noncomputable def commonSchedule (z : ℕ → GaussianInt) (ns : List ℕ) (N : ℕ) : ForwardKernel :=
  ns.foldr (fun n K => (differenceKernel z n).then K) (smoothingKernel N)

@[simp] lemma commonSchedule_bound (z : ℕ → GaussianInt) (ns : List ℕ) (N : ℕ) :
    (commonSchedule z ns N).bound = ns.sum+N := by
  induction ns with
  | nil => simp [commonSchedule,smoothingKernel]
  | cons n ns ih =>
    change n+(commonSchedule z ns N).bound = _
    rw [ih,List.sum_cons,Nat.add_assoc]

@[simp] lemma commonSchedule_cons (z : ℕ → GaussianInt) (n : ℕ) (ns : List ℕ) (N : ℕ) :
    commonSchedule z (n::ns) N = (differenceKernel z n).then (commonSchedule z ns N) := rfl

noncomputable def TimeLaw.advance (P : TimeLaw) (K : ForwardKernel) : TimeLaw where
  last := P.last+K.bound
  law := (P.law.joint (fun a => K.law a.val)).map (addOffsets P.last K.bound)

lemma ForwardKernel.displacement_entropy (K : ForwardKernel) (a : ℕ)
    (z : ℕ → GaussianInt) {D : ℝ} (hD : 1 ≤ D)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) (hK : 1 ≤ K.bound) :
    (K.law a).Hf (fun i => z (a+i.val)-z a) ≤
      Real.log 36+2*Real.log (D*K.bound) := by
  apply displacement_entropy_le
  · exact one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast hK)
  · intro i
    simpa only [Nat.add_zero] using walk_pair_displacement z (by linarith only [hD]) hstep
      a K.bound i.val 0 (by omega) (by omega)

lemma TimeLaw.advance_displacement_entropy (P : TimeLaw) (K : ForwardKernel)
    (z : ℕ → GaussianInt) {D : ℝ} (hD : 1 ≤ D)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) (hK : 1 ≤ K.bound) :
    (P.law.joint (fun a => K.law a.val)).Hf
      (fun v => z (v.1.val+v.2.val)-z v.1.val) ≤
      Real.log 36+2*Real.log (D*K.bound) := by
  apply displacement_entropy_le
  · exact one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast hK)
  · intro v
    simpa only [Nat.add_zero] using walk_pair_displacement z (by linarith only [hD]) hstep
      v.1.val K.bound v.2.val 0 (by omega) (by omega)

lemma entropy_step_deficit {b q : ℕ} {L F E E' g e C : ℝ}
    (hq : 0 < q) (hL : 0 ≤ L) (hg : 0 ≤ g) (hg1 : g ≤ 1/100)
    (hbq : (b:ℝ) ≤ g*q) (hF : (1-30*g)*L ≤ F)
    (hE : (1-e)*(q:ℝ)*L ≤ E) (hC : C ≤ 8*g*q*L)
    (hstep : (b:ℝ)*((q-b:ℕ)*F+E-C) ≤ 2*(q:ℝ)*E') :
    (1-e/2-20*g)*(b:ℝ)*L ≤ E' := by
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  have hbqr : (b:ℝ) ≤ q := by nlinarith only [hbq,hg1,hqr]
  have hbqnat : b ≤ q := by exact_mod_cast hbqr
  rw [Nat.cast_sub hbqnat] at hstep
  have hqbn : 0 ≤ (q:ℝ)-b := by linarith only [hbqr]
  have hFb := mul_le_mul_of_nonneg_left hF hqbn
  have hgl : 0 ≤ (1-30*g)*L := mul_nonneg (by linarith only [hg1]) hL
  have hbL := mul_le_mul_of_nonneg_right hbq hgl
  have hgg := mul_nonneg (mul_nonneg hg hg) (mul_nonneg hqr.le hL)
  have hgql : 0 ≤ g*(q:ℝ)*L := by positivity
  have hcore : (2-e-40*g)*(q:ℝ)*L ≤ ((q:ℝ)-b)*F+E-C := by
    linarith only [hFb,hbL,hE,hC,hgg,hgql]
  have hm := mul_le_mul_of_nonneg_left hcore (Nat.cast_nonneg b : (0:ℝ) ≤ b)
  apply (mul_le_mul_iff_right₀ (mul_pos (by norm_num : (0:ℝ)<2) hqr)).mp
  calc
    _ = (b:ℝ)*((2-e-40*g)*(q:ℝ)*L) := by ring
    _ ≤ (b:ℝ)*(((q:ℝ)-b)*F+E-C) := hm
    _ ≤ _ := hstep

theorem TimeLaw.step_deficit (P : TimeLaw) (s : SplitSieve)
    (z : ℕ → GaussianInt) {D g e : ℝ} (hD : 1 ≤ D)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) {n b q : ℕ}
    (hn : 1 ≤ n) (hb : 0 < b) (hbq : b < q) (hq : q ≤ s.primes.card)
    (hg : 0 ≤ g) (hg1 : g ≤ 1/100) (hL : 0 ≤ s.meanLog)
    (hratio : (b:ℝ) ≤ g*q)
    (hfresh : ∀ a : Fin (P.last+1), (1-30*g)*s.meanLog ≤ s.freshCoordinate
      (differenceLaw (fun t => z (a.val+t)) n)
      (fun ij => z (a.val+ij.1.val)) (fun ij => z (a.val+ij.2.val)) b (by omega))
    (hE : (1-e)*(q:ℝ)*s.meanLog ≤ s.pointEntropy P.law (fun a => z a.val) q)
    (hcost : 2*(Real.log 36+2*Real.log (D*n)) ≤ 8*g*q*s.meanLog) :
    (1-e/2-20*g)*(b:ℝ)*s.meanLog ≤
      s.pointEntropy (P.step z n).law (fun a => z a.val) b := by
  exact entropy_step_deficit (by omega) hL hg hg1 hratio le_rfl hE hcost
    (P.step_enrichment s z hD hstep hn hb hbq hq hfresh)

lemma deficit_iteration (l : ℕ) {g : ℝ} (hg : 0 ≤ g) (e : ℕ → ℝ)
    (h0 : e 0 ≤ 1) (hnext : ∀ j < l, e (j+1) ≤ e j/2+20*g) :
    e l ≤ (1/2:ℝ)^l+40*g := by
  induction l with
  | zero => simpa only [pow_zero] using h0.trans (le_add_of_nonneg_right (by positivity))
  | succ l ih =>
    have hi := ih (fun j hj => hnext j (by omega))
    have hn := hnext l (by omega)
    rw [pow_succ]
    linarith only [hi,hn]

end

section
namespace FinLaw
open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]

lemma joint_observation_fun (p : FinLaw Ω) (q : Ω → FinLaw α) (F : Ω × α → β) :
    (p.joint q).map F = p.mix (fun ω => (q ω).map (fun a => F (ω,a))) := by
  exact joint_observation p q (fun ω a => F (ω,a))

lemma mix_comm (p : FinLaw Ω) (q : FinLaw α) (r : Ω → α → FinLaw β) :
    p.mix (fun ω => q.mix (r ω)) = q.mix (fun a => p.mix (fun ω => r ω a)) := by
  ext b
  simp only [mix_mass,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro ω _
  ring

end FinLaw
open scoped BigOperators Classical

lemma TimeLaw.advance_difference (P : TimeLaw) (z : ℕ → GaussianInt) (n : ℕ) :
    P.advance (differenceKernel z n) = P.step z n := by
  unfold TimeLaw.advance TimeLaw.step differenceKernel
  congr 1
  dsimp only
  rw [FinLaw.joint_observation_fun]
  conv_lhs => arg 2; ext a; rw [FinLaw.map_comp,FinLaw.joint_observation_fun]
  rw [FinLaw.mix_comm,FinLaw.joint_observation_fun]
  conv_rhs => arg 2; ext c; rw [FinLaw.joint_observation_fun]
  apply congrArg
  funext c
  apply congrArg
  funext a
  apply congrArg
  funext ij
  apply Fin.ext
  dsimp only [Function.comp_def,addOffsets,endpointTime]
  split_ifs <;> rfl

end

namespace FinLaw
open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} {δ : Type uDelta} {ε : Type uEpsilon} [Fintype Ω]

noncomputable def cIf (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (O : Ω → γ) : ℝ :=
  p.cHf X O-p.cHf X (fun ω => (O ω,Y ω))

lemma cIf_nonneg (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (O : Ω → γ) :
    0 ≤ p.cIf X Y O := sub_nonneg.mpr (p.cHf_mono X O Y)

lemma cIf_comm (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (O : Ω → γ) :
    p.cIf X Y O = p.cIf Y X O := by
  unfold cIf cHf
  have he : p.Hf (fun ω => (X ω,(O ω,Y ω))) =
      p.Hf (fun ω => (Y ω,(O ω,X ω))) := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    simp only [Prod.mk.injEq]
    tauto
  rw [he,p.Hf_pair_comm O Y,p.Hf_pair_comm O X]
  ring

lemma cIf_le_cHf (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (O : Ω → γ) :
    p.cIf X Y O ≤ p.cHf X O := by
  have h := p.cHf_nonneg X (fun ω => (O ω,Y ω))
  unfold cIf
  linarith

lemma cIf_le_Hf (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (O : Ω → γ) :
    p.cIf X Y O ≤ p.Hf Y := by
  rw [p.cIf_comm]
  exact (p.cIf_le_cHf Y X O).trans (p.cHf_le_Hf Y O)

lemma cIf_chain (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → δ) (O : Ω → γ) :
    p.cIf X (fun ω => (Y ω,Z ω)) O =
      p.cIf X Y O+p.cIf X Z (fun ω => (O ω,Y ω)) := by
  unfold cIf
  have he : p.cHf X (fun ω => (O ω,(Y ω,Z ω))) =
      p.cHf X (fun ω => ((O ω,Y ω),Z ω)) := by
    unfold cHf
    rw [p.Hf_pair_assoc O Y Z]
    congr 1
    apply p.Hf_eq_of_fibers
    intro ω ν
    simp only [Prod.mk.injEq,and_assoc]
  rw [he]
  ring

lemma cIf_conditioning_cost (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β)
    (O : Ω → γ) (S : Ω → δ) :
    p.cIf X Y (fun ω => (O ω,S ω)) ≤ p.cIf X Y O+p.Hf S := by
  have h1 := p.cHf_mono X O S
  have h2 := p.cHf_mono S O Y
  have h3 := p.cHf_le_Hf S O
  have h4 := p.cHf_nonneg S (fun ω => (X ω,(O ω,Y ω)))
  have h5 := p.cHf_chain X S (fun ω => (O ω,Y ω))
  have h6 := p.cHf_chain S X (fun ω => (O ω,Y ω))
  have he : p.cHf (fun ω => (X ω,S ω)) (fun ω => (O ω,Y ω)) =
      p.cHf (fun ω => (S ω,X ω)) (fun ω => (O ω,Y ω)) := by
    unfold cHf
    congr 1
    apply p.Hf_eq_of_fibers
    intro ω ν
    simp only [Prod.mk.injEq]
    tauto
  have he' : p.cHf X (fun ω => ((O ω,S ω),Y ω)) =
      p.cHf X (fun ω => (S ω,(O ω,Y ω))) := by
    unfold cHf
    congr 1 <;> apply p.Hf_eq_of_fibers <;> intro ω ν <;>
      simp only [Prod.mk.injEq] <;> tauto
  unfold cIf
  rw [he']
  linarith only [h1,h2,h3,h4,h5,h6,he]

theorem cIf_transport (p : FinLaw Ω) (X : Ω → α) (O : Ω → β)
    (X' : Ω → γ) (O' : Ω → δ) (W : Ω → ε) {ζ : Type uZeta} (S : Ω → ζ)
    (hO : ∀ ω ν, (O ω,S ω)=(O ν,S ν) ↔ (O' ω,S ω)=(O' ν,S ν))
    (hX : ∀ ω ν, (X ω,O ω,S ω)=(X ν,O ν,S ν) ↔
      (X' ω,O' ω,S ω)=(X' ν,O' ν,S ν)) :
    p.cIf X (fun ω => (S ω,W ω)) O ≤ p.cIf X' W O'+2*p.Hf S := by
  have he : p.cIf X W (fun ω => (O ω,S ω)) =
      p.cIf X' W (fun ω => (O' ω,S ω)) := by
    rw [p.cIf_comm X W,p.cIf_comm X' W]
    unfold cIf cHf
    congr 2
    · apply p.Hf_eq_of_fibers
      intro ω ν
      simp only [Prod.mk.injEq,hO]
    · exact p.Hf_eq_of_fibers _ _ hO
    · apply p.Hf_eq_of_fibers
      intro ω ν
      have hh := hX ω ν
      simp only [Prod.mk.injEq] at hh ⊢
      tauto
    · apply p.Hf_eq_of_fibers
      intro ω ν
      have hh := hX ω ν
      simp only [Prod.mk.injEq] at hh ⊢
      tauto
  rw [p.cIf_chain X S W O,he]
  have h1 := p.cIf_le_Hf X S O
  have h2 := p.cIf_conditioning_cost X' W O' S
  linarith

lemma cHf_eq_conditionOn [Fintype β] (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.cHf X Y = ∑ a, p.map Y a*(p.conditionOn Y a).Hf X := by
  let C := outputCode X
  have hh := p.condH_eq_conditionOn C Y
  have hx (r : FinLaw Ω) : r.Hf C = r.Hf X := by
    apply r.Hf_eq_of_fibers
    intro ω ν
    exact outputCode_eq_iff X ω ν
  have hpair : p.Hf (fun ω => (C ω,Y ω)) = p.Hf (fun ω => (X ω,Y ω)) := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    simp only [Prod.mk.injEq,C,outputCode_eq_iff]
  simpa only [condH,← Hf_eq_H,hx,hpair,cHf] using hh

end FinLaw

open scoped BigOperators Classical

theorem SplitSieve.pointEntropy_shift {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve) (p : FinLaw Ω) (X Y : Ω → GaussianInt) (b : ℕ) :
    s.pointEntropy p X b ≤ s.pointEntropy p Y b+p.Hf (fun ω => Y ω-X ω) := by
  have h (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) :
      p.Hf (FinLaw.prefixVar (fun ω => s.residueVector σ (X ω)) π b) ≤
        p.Hf (FinLaw.prefixVar (fun ω => s.residueVector σ (Y ω)) π b)+
          p.Hf (fun ω => Y ω-X ω) := by
    apply (p.Hf_le_of_determined _ (fun ω =>
      (FinLaw.prefixVar (fun ν => s.residueVector σ (Y ν)) π b ω,Y ω-X ω)) ?_).trans
      (p.Hf_pair_subadd _ _)
    intro ω ν hh
    funext i
    by_cases hi : i.val<b
    · have hy : s.residueVector σ (Y ω) (π i)=s.residueVector σ (Y ν) (π i) := by
        simpa [FinLaw.prefixVar,hi] using congrFun (congrArg Prod.fst hh) i
      have hd := congrArg (residueCode (signedFactor (s.factor (s.enumeration (π i))) (σ (π i)))) (congrArg Prod.snd hh)
      have hx := residueCode_sub hy hd
      simpa only [sub_sub_cancel,SplitSieve.residueVector,FinLaw.prefixVar,hi,ite_eq_left]
        using congrArg some hx
    · simp [FinLaw.prefixVar,hi]
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ => h σ π))
  simpa only [SplitSieve.pointEntropy,FinLaw.signedEntropy,FinLaw.orderedEntropy,
    Finset.expect_add_distrib,Fintype.expect_const] using hh

lemma residue_observation_shift {Ω : Type uOmega} {ι : Type uIota} (f : ι → GaussianInt)
    (X Y : Ω → GaussianInt) (ω ν : Ω) :
    ((fun i => residueCode (f i) (X ω)),Y ω-X ω)=
      ((fun i => residueCode (f i) (X ν)),Y ν-X ν) ↔
    ((fun i => residueCode (f i) (Y ω)),Y ω-X ω)=
      ((fun i => residueCode (f i) (Y ν)),Y ν-X ν) := by
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨hx,hd⟩
    refine ⟨?_,hd⟩
    funext i
    have h := residueCode_add (congrFun hx i) (congrArg (residueCode (f i)) hd)
    simpa only [add_sub_cancel] using h
  · rintro ⟨hy,hd⟩
    refine ⟨?_,hd⟩
    funext i
    have h := residueCode_sub (congrFun hy i) (congrArg (residueCode (f i)) hd)
    simpa only [sub_sub_cancel] using h

end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat
open scoped BigOperators Classical

structure EnrichmentMargins (s : SplitSieve) (D g : ℝ) (n b q : ℕ) : Prop where
  length_pos : 1 ≤ n
  output_pos : 0 < b
  decreases : b < q
  input_cap : q ≤ s.primes.card
  ratio : (b:ℝ) ≤ g*q
  log_pos : 0 < Real.log n-Real.log 18
  rounding : s.meanLog ≤ g*(Real.log n-Real.log 18)
  large : 5120*s.meanLog ≤ g^4*(Real.log n-Real.log 18)
  output_cost : (b:ℝ)*s.meanLog ≤ g*(Real.log n-Real.log 18)
  lattice_cost : Real.log 16+Real.log (max D ((latticeBall (4*D)).card:ℝ)) ≤
    g*(Real.log n-Real.log 18)
  geometry_cap : 2*(2*Real.log n+Real.log 16+2*Real.log D) ≤ s.primes.card*s.meanLog
  displacement_cost : 2*(Real.log 36+2*Real.log (D*n)) ≤ 8*g*q*s.meanLog

theorem TimeLaw.geometric_step_deficit (P : TimeLaw) (s : SplitSieve)
    (hne : s.primes.Nonempty) (z : ℕ → GaussianInt) (hinj : Function.Injective z)
    {D T g e : ℝ} (hD : 1 ≤ D) (hT : 5 ≤ T)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    (hpT : ∀ p ∈ s.primes, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hg : 0 < g) (hg1 : g ≤ 1/100) (hL : 1 ≤ s.meanLog) {n b q : ℕ}
    (hm : EnrichmentMargins s D g n b q)
    (hE : (1-e)*(q:ℝ)*s.meanLog ≤ s.pointEntropy P.law (fun a => z a.val) q) :
    (1-e/2-20*g)*(b:ℝ)*s.meanLog ≤
      s.pointEntropy (P.step z n).law (fun a => z a.val) b := by
  apply P.step_deficit s z hD hstep hm.length_pos hm.output_pos hm.decreases
    hm.input_cap hg.le hg1 (by linarith only [hL]) hm.ratio ?_ hE hm.displacement_cost
  intro a
  obtain ⟨hb,hh⟩ := s.walk_fresh_lower hne (fun t => z (a.val+t)) hm.length_pos
    (shifted_walk_injective z hinj a.val) hD hT
    (fun t _ => by simpa only [Nat.add_assoc] using hstep (a.val+t)) hpT hg hg1 hL
    hm.log_pos hm.rounding hm.large hm.output_cost hm.lattice_cost hm.geometry_cap
  exact hh

lemma SplitSieve.pointEntropy_nonneg {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve) (p : FinLaw Ω) (Z : Ω → GaussianInt) (b : ℕ) :
    0 ≤ s.pointEntropy p Z b := by
  unfold pointEntropy FinLaw.signedEntropy
  exact Finset.expect_nonneg (fun _ _ => p.orderedEntropy_nonneg _ _)

noncomputable def TimeLaw.run (P : TimeLaw) (z : ℕ → GaussianInt) (n : ℕ → ℕ) : ℕ → TimeLaw
  | 0 => P
  | j+1 => (P.run z n j).step z (n j)

@[simp] lemma TimeLaw.run_zero (P : TimeLaw) (z : ℕ → GaussianInt) (n : ℕ → ℕ) :
    P.run z n 0=P := rfl
@[simp] lemma TimeLaw.run_succ (P : TimeLaw) (z : ℕ → GaussianInt) (n : ℕ → ℕ) (j : ℕ) :
    P.run z n (j+1)=(P.run z n j).step z (n j) := rfl

theorem TimeLaw.run_entropy (P : TimeLaw) (s : SplitSieve) (hne : s.primes.Nonempty)
    (z : ℕ → GaussianInt) (hinj : Function.Injective z) {D T g : ℝ}
    (hD : 1 ≤ D) (hT : 5 ≤ T) (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    (hpT : ∀ p ∈ s.primes, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hg : 0 < g) (hg1 : g ≤ 1/100) (hL : 1 ≤ s.meanLog)
    (n q : ℕ → ℕ) (l : ℕ) (hm : ∀ j<l, EnrichmentMargins s D g (n j) (q (j+1)) (q j)) :
    (1-(1/2:ℝ)^l-40*g)*(q l:ℝ)*s.meanLog ≤
      s.pointEntropy (P.run z n l).law (fun a => z a.val) (q l) := by
  induction l with
  | zero =>
    have hh := s.pointEntropy_nonneg P.law (fun a => z a.val) (q 0)
    simp only [pow_zero,sub_self,zero_sub,TimeLaw.run_zero]
    have hneg : -(40*g)*(q 0:ℝ)*s.meanLog ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hg]) (Nat.cast_nonneg (q 0))
      · linarith only [hL]
    exact hneg.trans hh
  | succ l ih =>
    have hi := ih (fun j hj => hm j (by omega))
    have hh := (P.run z n l).geometric_step_deficit s hne z hinj hD hT hstep hpT
      hg hg1 hL (hm l (by omega)) (e := (1/2:ℝ)^l+40*g) (by
        convert hi using 1; ring)
    rw [TimeLaw.run_succ]
    convert hh using 1; ring

theorem TimeLaw.advance_entropy (P : TimeLaw) (K : ForwardKernel) (s : SplitSieve)
    (z : ℕ → GaussianInt) {D : ℝ} (hD : 1 ≤ D)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) (hK : 1 ≤ K.bound) (b : ℕ) :
    s.pointEntropy P.law (fun a => z a.val) b -
      (Real.log 36+2*Real.log (D*K.bound)) ≤
    s.pointEntropy (P.advance K).law (fun a => z a.val) b := by
  let Q := P.law.joint (fun a => K.law a.val)
  have hh := s.pointEntropy_shift Q (fun v => z v.1.val)
    (fun v => z (v.1.val+v.2.val)) b
  have hfst := s.pointEntropy_joint_fst P.law (fun a => K.law a.val) (fun a => z a.val) b
  change s.pointEntropy Q (fun v => z v.1.val) b = _ at hfst
  rw [hfst] at hh
  have he : s.pointEntropy (P.advance K).law (fun a => z a.val) b =
      s.pointEntropy Q (fun v => z (v.1.val+v.2.val)) b := by
    unfold TimeLaw.advance
    rw [s.pointEntropy_map]
    rfl
  rw [he]
  have hc := P.advance_displacement_entropy K z hD hstep hK
  linarith only [hh,hc]

theorem TimeLaw.run_future_entropy (P : TimeLaw) (K : ForwardKernel) (s : SplitSieve)
    (hne : s.primes.Nonempty) (z : ℕ → GaussianInt) (hinj : Function.Injective z)
    {D T g : ℝ} (hD : 1 ≤ D) (hT : 5 ≤ T)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    (hpT : ∀ p ∈ s.primes, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hg : 0 < g) (hg1 : g ≤ 1/100) (hL : 1 ≤ s.meanLog)
    (n q : ℕ → ℕ) (l : ℕ) (hm : ∀ j<l, EnrichmentMargins s D g (n j) (q (j+1)) (q j))
    (hK : 1 ≤ K.bound) {e : ℝ}
    (hcost : Real.log 36+2*Real.log (D*K.bound) ≤ e*(q l:ℝ)*s.meanLog) :
    (1-(1/2:ℝ)^l-40*g-e)*(q l:ℝ)*s.meanLog ≤
      s.pointEntropy ((P.run z n l).advance K).law (fun a => z a.val) (q l) := by
  have h1 := P.run_entropy s hne z hinj hD hT hstep hpT hg hg1 hL n q l hm
  have h2 := (P.run z n l).advance_entropy K s z hD hstep hK (q l)
  linarith only [h1,h2,hcost]

noncomputable def TimeLaw.observe {α : Type uAlpha} [Fintype α] (P : TimeLaw) (f : ℕ → α) : FinLaw α :=
  P.law.map (fun t => f t.val)

lemma TimeLaw.ext_observe (P Q : TimeLaw) (hl : P.last=Q.last)
    (h : ∀ {α : Type} [Fintype α] (f : ℕ → α), P.observe f=Q.observe f) : P=Q := by
  cases P with | mk n p =>
  cases Q with | mk m q =>
  dsimp only at hl
  subst m
  congr 1
  let f : ℕ → Fin (n+1) := fun t => ⟨min t n,by omega⟩
  have hh := h f
  have he : (fun t : Fin (n+1) => f t.val)=id := by
    funext t
    apply Fin.ext
    exact Nat.min_eq_left (by omega)
  unfold observe at hh
  simpa only [he,FinLaw.map_id] using hh

lemma TimeLaw.observe_advance {α : Type uAlpha} [Fintype α]
    (P : TimeLaw) (K : ForwardKernel) (f : ℕ → α) :
    (P.advance K).observe f=P.law.mix (fun a => (K.law a.val).map (fun t => f (a.val+t.val))) := by
  unfold observe advance
  rw [FinLaw.map_comp,FinLaw.joint_observation_fun]
  rfl

lemma ForwardKernel.then_observe {α : Type uAlpha} [Fintype α]
    (K R : ForwardKernel) (a : ℕ) (f : ℕ → α) :
    ((K.then R).law a).map (fun t => f (a+t.val))=
      (K.law a).mix (fun t => (R.law (a+t.val)).map (fun u => f (a+t.val+u.val))) := by
  unfold ForwardKernel.then
  rw [FinLaw.map_comp,FinLaw.joint_observation_fun]
  congr 1
  funext t
  congr 1
  funext u
  simp only [Function.comp_def,addOffsets,Nat.add_assoc]

lemma TimeLaw.advance_then (P : TimeLaw) (K R : ForwardKernel) :
    P.advance (K.then R)=(P.advance K).advance R := by
  apply TimeLaw.ext_observe
  · exact (Nat.add_assoc _ _ _).symm
  · intro α _ f
    rw [TimeLaw.observe_advance,TimeLaw.observe_advance]
    change P.law.mix _ = (((P.law.joint (fun a => K.law a.val)).map
      (addOffsets P.last K.bound))).mix (fun a : Fin (P.last+K.bound+1) =>
        (R.law a.val).map (fun t => f (a.val+t.val)))
    rw [FinLaw.mix_map_left]
    have hj := FinLaw.joint_observation (P.law) (fun a => K.law a.val)
      (fun a t => (a,t))
    clear hj
    have hmix : ((P.law.joint (fun a => K.law a.val))).mix
        (fun v => (R.law (v.1.val+v.2.val)).map (fun u => f (v.1.val+v.2.val+u.val))) =
      P.law.mix (fun a => (K.law a.val).mix
        (fun t => (R.law (a.val+t.val)).map (fun u => f (a.val+t.val+u.val)))) := by
      ext x
      simp only [FinLaw.mix_mass,FinLaw.joint_mass,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
    change P.law.mix _ = (P.law.joint (fun a => K.law a.val)).mix
      (fun v => (R.law (v.1.val+v.2.val)).map (fun u => f (v.1.val+v.2.val+u.val)))
    rw [hmix]
    congr 1
    funext a
    exact K.then_observe R a.val f

lemma TimeLaw.advance_common_cons (P : TimeLaw) (z : ℕ → GaussianInt)
    (n : ℕ) (ns : List ℕ) (N : ℕ) :
    P.advance (commonSchedule z (n::ns) N)=(P.step z n).advance (commonSchedule z ns N) := by
  rw [commonSchedule_cons,TimeLaw.advance_then,TimeLaw.advance_difference]

lemma TimeLaw.advance_common_append (P : TimeLaw) (z : ℕ → GaussianInt)
    (ns ms : List ℕ) (N : ℕ) :
    P.advance (commonSchedule z (ns++ms) N)=
      (ns.foldl (fun Q k => Q.step z k) P).advance (commonSchedule z ms N) := by
  induction ns generalizing P with
  | nil => rfl
  | cons k ks hk =>
    rw [List.cons_append,TimeLaw.advance_common_cons,hk,List.foldl_cons]

lemma TimeLaw.foldl_ofFn (P : TimeLaw) (z : ℕ → GaussianInt)
    (n : ℕ → ℕ) (l : ℕ) :
    (List.ofFn (fun i : Fin l => n i.val)).foldl (fun Q k => Q.step z k) P=P.run z n l := by
  induction l with
  | zero => rfl
  | succ l hl =>
    rw [List.ofFn_succ_last,List.foldl_append,List.foldl_cons,List.foldl_nil]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [hl,TimeLaw.run_succ]

lemma TimeLaw.run_common (P : TimeLaw) (z : ℕ → GaussianInt)
    (n : ℕ → ℕ) (l N : ℕ) :
    P.advance (commonSchedule z (List.ofFn (fun i : Fin l => n i.val)) N)=
      (P.run z n l).advance (smoothingKernel N) := by
  have h := P.advance_common_append z (List.ofFn (fun i : Fin l => n i.val)) [] N
  simpa only [List.append_nil,TimeLaw.foldl_ofFn,commonSchedule,List.foldr_nil] using h

lemma log_floor_exp {x : ℝ} (hx : 2 ≤ x) :
    1 ≤ ⌊Real.exp x⌋₊ ∧ x-1 ≤ Real.log (⌊Real.exp x⌋₊:ℝ) ∧
      Real.log (⌊Real.exp x⌋₊:ℝ) ≤ x := by
  have he : 2 ≤ Real.exp x := by linarith only [Real.add_one_le_exp x,hx]
  have hn : 1 ≤ ⌊Real.exp x⌋₊ := Nat.floor_pos.mpr (by linarith only [he])
  have hnp : (0:ℝ)<⌊Real.exp x⌋₊ := by exact_mod_cast hn
  have hlow : Real.exp x/2 ≤ (⌊Real.exp x⌋₊:ℝ) := by
    have h := Nat.lt_floor_add_one (Real.exp x)
    linarith only [he,h]
  have hlo := Real.log_le_log (div_pos (Real.exp_pos x) (by norm_num : (0:ℝ)<2)) hlow
  rw [Real.log_div (Real.exp_ne_zero x) (by norm_num : (2:ℝ)≠0),Real.log_exp] at hlo
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith only [h]
  have hhi := Real.log_le_log hnp (Nat.floor_le (Real.exp_nonneg x))
  rw [Real.log_exp] at hhi
  exact ⟨hn,by linarith only [hlo,hl2],hhi⟩

theorem EnrichmentMargins.from_scale (s : SplitSieve) {D U g : ℝ}
    (hD : 1 ≤ D) (hg : 0 < g) (hg1 : g ≤ 1/200) (hL : 1 ≤ s.meanLog)
    (hU : 0 < U)
    (hlog : 2*(1+Real.log 18) ≤ g*U)
    (hlarge : 640*s.meanLog ≤ g^5*U)
    (hsize : Real.log 16+Real.log (max D ((latticeBall (4*D)).card:ℝ)) ≤ g^2*U)
    (hdisp : 4*Real.log D+2*Real.log 36 ≤ 4*g*U)
    (hgeom : 2*Real.log 16+4*Real.log D ≤ U/4)
    (hcap : ⌊U/s.meanLog⌋₊ ≤ s.primes.card) :
    EnrichmentMargins s D (2*g) ⌊Real.exp (g*U)⌋₊
      ⌊g^2*U/s.meanLog⌋₊ ⌊U/s.meanLog⌋₊ := by
  let L := s.meanLog
  let n := ⌊Real.exp (g*U)⌋₊
  let q := ⌊U/L⌋₊
  let b := ⌊g^2*U/L⌋₊
  have hLp : 0 < L := by dsimp [L]; linarith only [hL]
  have hg_le : g ≤ 1 := by linarith only [hg1]
  have hg2 : g^2 ≤ 1 := pow_le_one₀ hg.le hg_le
  have hg3 : g^3 ≤ 1 := pow_le_one₀ hg.le hg_le
  have h52 : g^5*U ≤ g^2*U := by
    have hpow : g^5=g^2*g^3 := by ring
    rw [hpow]
    nlinarith only [hg3,mul_nonneg (sq_nonneg g) hU.le]
  have h2U : g^2*U ≤ U := by nlinarith only [hg2,hU]
  have hLU : L ≤ U/2 := by
    change 640*L ≤ g^5*U at hlarge
    linarith only [hlarge,h52,h2U,hLp]
  have hbL : L ≤ g^2*U := by
    change 640*L ≤ g^5*U at hlarge
    linarith only [hlarge,h52,hLp]
  have he2 : 2 ≤ g*U := by
    have hh := Real.log_nonneg (by norm_num : (1:ℝ)≤18)
    linarith only [hh,hlog]
  obtain ⟨hn,hnlo,hnhi⟩ := log_floor_exp he2
  have hnlo' : g*U/2 ≤ Real.log n-Real.log 18 := by
    change g*U-1 ≤ Real.log n at hnlo
    linarith only [hnlo,hlog]
  have hu : 0 < Real.log n-Real.log 18 :=
    lt_of_lt_of_le (div_pos (mul_pos hg hU) (by norm_num)) hnlo'
  have hqL : U-L ≤ (q:ℝ)*L := by
    have hf := Nat.lt_floor_add_one (U/L)
    have hm := mul_lt_mul_of_pos_right hf hLp
    rw [div_mul_cancel₀ _ hLp.ne',add_mul,one_mul] at hm
    linarith only [hm]
  have hqU : U/2 ≤ (q:ℝ)*L := by linarith only [hqL,hLU]
  have hqpos : 0 < q := by
    have : (0:ℝ)<q := by nlinarith only [hqU,hU,hLp]
    exact_mod_cast this
  have hbpos : 0 < b := by
    apply Nat.floor_pos.mpr
    exact (le_div_iff₀ hLp).mpr (by simpa only [one_mul] using hbL)
  have hbup : (b:ℝ)*L ≤ g^2*U := by
    exact (le_div_iff₀ hLp).mp (Nat.floor_le (by positivity : 0 ≤ g^2*U/L))
  have hratio : (b:ℝ) ≤ (2*g)*q := by
    have h1 := mul_le_mul_of_nonneg_left hqU (show 0 ≤ 2*g by positivity)
    have h2 : g^2*U ≤ g*U := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hg_le hg.le) hU.le
      simpa only [mul_one,pow_two] using hh
    apply (mul_le_mul_iff_left₀ hLp).mp
    linarith only [hbup,h1,h2]
  have hbq : b < q := by
    have hqr : (0:ℝ)<q := by exact_mod_cast hqpos
    have : (b:ℝ)<q := by nlinarith only [hratio,hg1,hqr]
    exact_mod_cast this
  refine ⟨hn,hbpos,hbq,hcap,hratio,hu,?_,?_,?_,?_,?_,?_⟩
  · have hm := mul_le_mul_of_nonneg_left hnlo' (show 0 ≤ 2*g by positivity)
    dsimp only [L] at hbL
    linarith only [hbL,hm]
  · have hm := mul_le_mul_of_nonneg_left hnlo' (show 0 ≤ (2*g)^4 by positivity)
    linarith only [hlarge,hm]
  · have hm := mul_le_mul_of_nonneg_left hnlo' (show 0 ≤ 2*g by positivity)
    change (b:ℝ)*L ≤ _
    linarith only [hbup,hm]
  · have hm := mul_le_mul_of_nonneg_left hnlo' (show 0 ≤ 2*g by positivity)
    linarith only [hsize,hm]
  · have hqcap : (q:ℝ)*L ≤ s.primes.card*L :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcap) hLp.le
    have hgU := mul_le_mul_of_nonneg_right hg1 hU.le
    change 2*(2*Real.log n+Real.log 16+2*Real.log D) ≤ s.primes.card*L
    change Real.log n ≤ g*U at hnhi
    linarith only [hnhi,hgeom,hqU,hqcap,hgU,hU]
  · have hm := mul_le_mul_of_nonneg_left hqU (show 0 ≤ 16*g by positivity)
    have hDn : D≠0 := by linarith only [hD]
    have hnR : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
    rw [Real.log_mul hDn hnR]
    change Real.log n ≤ g*U at hnhi
    change 2*(Real.log 36+2*(Real.log D+Real.log n)) ≤ 8*(2*g)*q*L
    linarith only [hnhi,hdisp,hm]

noncomputable def bandScale (g U : ℝ) (j : ℕ) : ℝ := (g^2)^j*U
noncomputable def bandLength (g U : ℝ) (j : ℕ) : ℕ := ⌊Real.exp (g*bandScale g U j)⌋₊
noncomputable def bandSize (s : SplitSieve) (g U : ℝ) (j : ℕ) : ℕ := ⌊bandScale g U j/s.meanLog⌋₊

lemma bandScale_pos {g U : ℝ} (hg : 0<g) (hU : 0<U) (j : ℕ) :
    0<bandScale g U j := mul_pos (pow_pos (sq_pos_of_pos hg) _) hU

lemma bandScale_antitone {g U : ℝ} (hg : 0≤g) (hg1 : g≤1) (hU : 0≤U) :
    Antitone (bandScale g U) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one (sq_nonneg g) (pow_le_one₀ hg hg1) hij) hU

lemma bandScale_succ (g U : ℝ) (j : ℕ) :
    bandScale g U (j+1)=g^2*bandScale g U j := by
  unfold bandScale
  rw [pow_succ]
  ring

theorem geometric_band_margins (s : SplitSieve) {D U g : ℝ} {l : ℕ}
    (hD : 1≤D) (hg : 0<g) (hg1 : g≤1/200) (hL : 1 ≤ s.meanLog) (hU : 0<U)
    (hlog : 2*(1+Real.log 18) ≤ g*bandScale g U l)
    (hlarge : 640*s.meanLog ≤ g^5*bandScale g U l)
    (hsize : Real.log 16+Real.log (max D ((latticeBall (4*D)).card:ℝ)) ≤ g^2*bandScale g U l)
    (hdisp : 4*Real.log D+2*Real.log 36 ≤ 4*g*bandScale g U l)
    (hgeom : 2*Real.log 16+4*Real.log D ≤ bandScale g U l/4)
    (hcap : ⌊U/s.meanLog⌋₊ ≤ s.primes.card) :
    ∀ j<l, EnrichmentMargins s D (2*g) (bandLength g U j)
      (bandSize s g U (j+1)) (bandSize s g U j) := by
  intro j hj
  have hmono := bandScale_antitone hg.le (show g≤1 by linarith only [hg1]) hU.le
  have hlow := hmono hj.le
  have hhigh := hmono (Nat.zero_le j)
  simp only [bandScale,pow_zero,one_mul] at hhigh
  unfold bandLength bandSize
  rw [bandScale_succ]
  apply EnrichmentMargins.from_scale s hD hg hg1 hL (bandScale_pos hg hU j)
  · exact hlog.trans (mul_le_mul_of_nonneg_left hlow hg.le)
  · exact hlarge.trans (mul_le_mul_of_nonneg_left hlow (pow_nonneg hg.le _))
  · exact hsize.trans (mul_le_mul_of_nonneg_left hlow (sq_nonneg g))
  · exact hdisp.trans (mul_le_mul_of_nonneg_left hlow (by positivity))
  · exact hgeom.trans (div_le_div_of_nonneg_right hlow (by norm_num))
  · exact (Nat.floor_mono (div_le_div_of_nonneg_right hhigh (by linarith only [hL]))).trans hcap

theorem TimeLaw.geometric_band_entropy (P : TimeLaw) (s : SplitSieve)
    (hne : s.primes.Nonempty) (z : ℕ → GaussianInt) (hinj : Function.Injective z)
    {D T U g : ℝ} {l : ℕ} (hD : 1≤D) (hT : 5≤T)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (hpT : ∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T)
    (hg : 0<g) (hg1 : g≤1/200) (hL : 1 ≤ s.meanLog) (hU : 0<U)
    (hlog : 2*(1+Real.log 18) ≤ g*bandScale g U l)
    (hlarge : 640*s.meanLog ≤ g^5*bandScale g U l)
    (hsize : Real.log 16+Real.log (max D ((latticeBall (4*D)).card:ℝ)) ≤ g^2*bandScale g U l)
    (hdisp : 4*Real.log D+2*Real.log 36 ≤ 4*g*bandScale g U l)
    (hgeom : 2*Real.log 16+4*Real.log D ≤ bandScale g U l/4)
    (hcap : ⌊U/s.meanLog⌋₊ ≤ s.primes.card) :
    (1-(1/2:ℝ)^l-80*g)*(bandSize s g U l:ℝ)*s.meanLog ≤
      s.pointEntropy (P.run z (bandLength g U) l).law (fun a => z a.val) (bandSize s g U l) := by
  have hm := geometric_band_margins s hD hg hg1 hL hU hlog hlarge hsize hdisp hgeom hcap
  have hh := P.run_entropy s hne z hinj hD hT hs hpT (by positivity : 0<2*g)
    (by linarith only [hg1] : 2*g≤1/100) hL (bandLength g U) (bandSize s g U) l hm
  convert hh using 1; ring

lemma commonSchedule_log_bound (z : ℕ → GaussianInt) (ns : List ℕ) (N : ℕ) {x : ℝ}
    (hns : ∀ n∈ns, (n:ℝ)≤Real.exp x) (hN : (N:ℝ)≤Real.exp x)
    (hlen : (ns.length+2:ℝ)≤Real.exp x) :
    Real.log (1+(commonSchedule z ns N).bound:ℝ) ≤ 2*x := by
  have hsum : (ns.sum:ℝ)≤(ns.length:ℝ)*Real.exp x := by
    induction ns with
    | nil => simp
    | cons n ns ih =>
      have hn := hns n (by simp)
      have ht := ih (fun k hk => hns k (by simp [hk]))
        (by simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hlen; linarith only [hlen])
      simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      linarith only [hn,ht]
  have hx : (1:ℝ)≤Real.exp x := by
    have hlen0 : (0:ℝ)≤ns.length := Nat.cast_nonneg _
    linarith only [hlen,hlen0]
  have hall : (1+(commonSchedule z ns N).bound:ℝ)≤Real.exp (2*x) := by
    rw [commonSchedule_bound,Nat.cast_add]
    have hm := mul_le_mul_of_nonneg_right hlen (Real.exp_nonneg x)
    rw [show 2*x=x+x by ring,Real.exp_add]
    linarith only [hsum,hN,hm,hx]
  have hlog := Real.log_le_log (by positivity : (0:ℝ)<1+(commonSchedule z ns N).bound) hall
  simpa only [Real.log_exp] using hlog

lemma suffix_entropy_cost {D g V L : ℝ} {q S : ℕ}
    (hD : 1≤D) (hg : 0≤g) (hS : 1≤S)
    (hq : V/2≤(q:ℝ)*L) (hlog : Real.log (1+(S:ℝ))≤2*g*V)
    (hconst : Real.log 36+2*Real.log D≤g*V) :
    Real.log 36+2*Real.log (D*S)≤10*g*q*L := by
  have hSp : (0:ℝ)<S := by exact_mod_cast hS
  have hSl := Real.log_le_log hSp (show (S:ℝ)≤1+S by linarith)
  rw [Real.log_mul (by linarith only [hD] : D≠0) hSp.ne']
  have hq' := mul_le_mul_of_nonneg_left hq (show 0≤10*g by positivity)
  linarith only [hSl,hlog,hconst,hq']

end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat
open scoped BigOperators Classical
namespace FinLaw
noncomputable def pure {Ω : Type uOmega} [Fintype Ω] (ω : Ω) : FinLaw Ω where
  mass ν := if ν=ω then 1 else 0
  nonneg _ := by split_ifs <;> norm_num
  sum_one := by simp

lemma mix_pure {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω] [Fintype α] (ω : Ω) (q : Ω → FinLaw α) :
    (pure ω).mix q=q ω := by
  ext a
  simp [mix_mass,pure]

lemma joint_pure_observation {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω] [Fintype α] [Fintype β]
    (ω : Ω) (q : Ω → FinLaw α) (F : Ω × α → β) :
    ((pure ω).joint q).map F=(q ω).map (fun a => F (ω,a)) := by
  rw [joint_observation_fun,mix_pure]
end FinLaw

noncomputable def TimeLaw.at (a : ℕ) : TimeLaw where
  last := a
  law := FinLaw.pure ⟨a,by omega⟩

lemma TimeLaw.at_advance (a : ℕ) (K : ForwardKernel) :
    ((TimeLaw.at a).advance K).law=
      (K.law a).map (fun t => (⟨a+t.val,by omega⟩ : Fin (a+K.bound+1))) := by
  change ((FinLaw.pure (⟨a,by omega⟩ : Fin (a+1))).joint
    (fun t => K.law t.val)).map (addOffsets a K.bound)=_
  rw [FinLaw.joint_pure_observation]
  rfl

lemma SplitSieve.pointEntropy_exact_start (s : SplitSieve) (K : ForwardKernel)
    (z : ℕ → GaussianInt) (a b : ℕ) :
    s.pointEntropy ((TimeLaw.at a).advance K).law (fun t => z t.val) b=
      s.pointEntropy (K.law a) (fun t => z (a+t.val)) b := by
  rw [TimeLaw.at_advance]
  change s.pointEntropy ((K.law a).map
    (fun t => (⟨a+t.val,by omega⟩ : Fin (a+K.bound+1)))) (fun t => z t.val) b = _
  rw [s.pointEntropy_map]
  rfl

theorem TimeLaw.advance_entropy_succ (P : TimeLaw) (K : ForwardKernel) (s : SplitSieve)
    (z : ℕ → GaussianInt) {D : ℝ} (hD : 1≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (b : ℕ) :
    s.pointEntropy P.law (fun a => z a.val) b-
      (Real.log 36+2*Real.log (D*(K.bound+1))) ≤
    s.pointEntropy (P.advance K).law (fun a => z a.val) b := by
  let Q := P.law.joint (fun a => K.law a.val)
  have hh := s.pointEntropy_shift Q (fun v => z v.1.val)
    (fun v => z (v.1.val+v.2.val)) b
  have hf := s.pointEntropy_joint_fst P.law (fun a => K.law a.val) (fun a => z a.val) b
  change s.pointEntropy Q (fun v => z v.1.val) b=_ at hf
  rw [hf] at hh
  have he : s.pointEntropy (P.advance K).law (fun a => z a.val) b=
      s.pointEntropy Q (fun v => z (v.1.val+v.2.val)) b := by
    unfold TimeLaw.advance
    rw [s.pointEntropy_map]
    rfl
  have hc : Q.Hf (fun v => z (v.1.val+v.2.val)-z v.1.val) ≤
      Real.log 36+2*Real.log (D*(K.bound+1)) := by
    apply displacement_entropy_le
    · exact one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast Nat.le_add_left 1 K.bound)
    · intro v
      have hd := walk_pair_displacement z (by linarith only [hD]) hs
        v.1.val (K.bound+1) v.2.val 0 (by omega) (by omega)
      simpa only [Nat.add_zero,Nat.cast_add,Nat.cast_one] using hd
  rw [he]
  linarith only [hh,hc]

theorem commonSchedule_subband_entropy (s : SplitSieve) (hne : s.primes.Nonempty)
    (z : ℕ → GaussianInt) (hinj : Function.Injective z)
    (pre post : List ℕ) (a N : ℕ) {D T U g e : ℝ} {l : ℕ}
    (hD : 1≤D) (hT : 5≤T) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (hpT : ∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T)
    (hg : 0<g) (hg1 : g≤1/200) (hL : 1≤ s.meanLog) (hU : 0<U)
    (hlog : 2*(1+Real.log 18)≤g*bandScale g U l)
    (hlarge : 640*s.meanLog≤g^5*bandScale g U l)
    (hsize : Real.log 16+Real.log (max D ((latticeBall (4*D)).card:ℝ))≤g^2*bandScale g U l)
    (hdisp : 4*Real.log D+2*Real.log 36≤4*g*bandScale g U l)
    (hgeom : 2*Real.log 16+4*Real.log D≤bandScale g U l/4)
    (hcap : ⌊U/s.meanLog⌋₊≤ s.primes.card)
    (hcost : Real.log 36+2*Real.log (D*((post.sum+N:ℕ)+1)) ≤
      e*(bandSize s g U l:ℝ)*s.meanLog) :
    (1-(1/2:ℝ)^l-80*g-e)*(bandSize s g U l:ℝ)*s.meanLog ≤
      s.pointEntropy ((commonSchedule z
        (pre++List.ofFn (fun i : Fin l => bandLength g U i.val)++post) N).law a)
          (fun t => z (a+t.val)) (bandSize s g U l) := by
  rw [← s.pointEntropy_exact_start]
  rw [List.append_assoc,TimeLaw.advance_common_append,TimeLaw.advance_common_append,
    TimeLaw.foldl_ofFn]
  let P := pre.foldl (fun Q k => Q.step z k) (TimeLaw.at a)
  have h1 := P.geometric_band_entropy s hne z hinj hD hT hs hpT hg hg1 hL hU
    hlog hlarge hsize hdisp hgeom hcap
  have h2 := (P.run z (bandLength g U) l).advance_entropy_succ
    (commonSchedule z post N) s z hD hs (bandSize s g U l)
  rw [commonSchedule_bound] at h2
  change _ ≤ s.pointEntropy ((P.run z (bandLength g U) l).advance (commonSchedule z post N)).law
    (fun a => z a.val) (bandSize s g U l)
  simp only [Nat.cast_add] at hcost h2
  linarith only [h1,h2,hcost]

lemma ForwardKernel.ext_observe (K R : ForwardKernel) (hb : K.bound=R.bound)
    (h : ∀ (a : ℕ) {α : Type} [Fintype α] (f : ℕ → α),
      (K.law a).map (fun t => f (a+t.val))=(R.law a).map (fun t => f (a+t.val))) : K=R := by
  cases K with | mk n p =>
  cases R with | mk m q =>
  dsimp only at hb
  subst m
  congr 1
  funext a
  let f : ℕ → Fin (n+1) := fun t => ⟨min (t-a) n,by omega⟩
  have hh := h a f
  have he : (fun t : Fin (n+1) => f (a+t.val))=id := by
    funext t
    apply Fin.ext
    dsimp only [f,id_eq]
    omega
  simpa only [he,FinLaw.map_id] using hh

lemma ForwardKernel.then_assoc (K R S : ForwardKernel) :
    (K.then R).then S=K.then (R.then S) := by
  apply ForwardKernel.ext_observe
  · exact Nat.add_assoc _ _ _
  · intro a α _ f
    rw [ForwardKernel.then_observe,ForwardKernel.then_observe]
    have hl : ((K.then R).law a).mix
        (fun t => (S.law (a+t.val)).map (fun u => f (a+t.val+u.val))) =
        (K.law a).mix (fun t => (R.law (a+t.val)).mix
          (fun u => (S.law (a+t.val+u.val)).map (fun v => f (a+t.val+u.val+v.val)))) := by
      unfold ForwardKernel.then
      rw [FinLaw.mix_map_left]
      ext x
      simp only [FinLaw.mix_mass,FinLaw.joint_mass,Fintype.sum_prod_type,Finset.mul_sum,
        addOffsets,Nat.add_assoc,mul_assoc]
    rw [hl]
    congr 1
    funext t
    exact (R.then_observe S (a+t.val) f).symm

lemma FinLaw.map_pure {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω] [Fintype α]
    (ω : Ω) (f : Ω → α) : (FinLaw.pure ω).map f=FinLaw.pure (f ω) := by
  ext a
  simp only [FinLaw.map_mass,FinLaw.pure]
  rw [Finset.sum_eq_single ω]
  · simp only [ite_true,eq_comm]
  · intro ν _ hν
    simp [hν]
  · simp

lemma FinLaw.mix_pure_right {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω] [Fintype α]
    (p : FinLaw Ω) (f : Ω → α) : p.mix (fun ω => FinLaw.pure (f ω))=p.map f := by
  ext a
  simp only [FinLaw.mix_mass,FinLaw.pure,FinLaw.map_mass,mul_ite,mul_one,mul_zero]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [eq_comm]

lemma smoothingKernel_zero_law (a : ℕ) :
    (smoothingKernel 0).law a=FinLaw.pure (0 : Fin 1) := by
  change FinLaw.uniform (Fin 1)=FinLaw.pure (0 : Fin 1)
  ext x
  have hx : x=0 := Subsingleton.elim _ _
  simp [FinLaw.uniform,FinLaw.pure,hx]

lemma ForwardKernel.then_zero (K : ForwardKernel) : K.then (smoothingKernel 0)=K := by
  apply ForwardKernel.ext_observe
  · exact Nat.add_zero _
  · intro a α _ f
    rw [ForwardKernel.then_observe]
    change (K.law a).mix (fun t => (FinLaw.uniform (Fin 1)).map
      (fun u => f (a+t.val+u.val)))=_
    have hu : FinLaw.uniform (Fin 1)=FinLaw.pure (0 : Fin 1) := smoothingKernel_zero_law 0
    simp only [hu,FinLaw.map_pure,Fin.val_zero,Nat.add_zero]
    exact FinLaw.mix_pure_right _ _

lemma ForwardKernel.zero_then (K : ForwardKernel) : (smoothingKernel 0).then K=K := by
  apply ForwardKernel.ext_observe
  · exact Nat.zero_add _
  · intro a α _ f
    rw [ForwardKernel.then_observe]
    change (FinLaw.uniform (Fin 1)).mix
      (fun t => (K.law (a+t.val)).map (fun u => f (a+t.val+u.val)))=_
    have hu : FinLaw.uniform (Fin 1)=FinLaw.pure (0 : Fin 1) := smoothingKernel_zero_law 0
    rw [hu,FinLaw.mix_pure]
    rfl

lemma commonSchedule_append (z : ℕ → GaussianInt) (ns ms : List ℕ) (N : ℕ) :
    commonSchedule z (ns++ms) N=(commonSchedule z ns 0).then (commonSchedule z ms N) := by
  induction ns with
  | nil => exact (ForwardKernel.zero_then _).symm
  | cons n ns ih =>
    rw [List.cons_append,commonSchedule_cons,commonSchedule_cons,ih,ForwardKernel.then_assoc]

end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat

section
open scoped BigOperators Classical
variable {G : Type uGroup} [Fintype G] [AddGroup G]

noncomputable def overlapCount (K E : Finset G) (x : G) : ℕ :=
  (E.filter (fun y => x+y ∈ K)).card

lemma overlapCount_sum (K E : Finset G) :
    (∑ x : G, overlapCount K E x) = K.card*E.card := by
  simp only [overlapCount,Finset.card_filter]
  rw [Finset.sum_comm]
  have hh (y : G) : (∑ x : G, if x+y ∈ K then (1:ℕ) else 0) = K.card := by
    calc
      _ = ∑ x : G, if x ∈ K then (1:ℕ) else 0 :=
        Equiv.sum_comp (Equiv.addRight y) (fun x => if x ∈ K then (1:ℕ) else 0)
      _ = K.card := by simp
  simp only [hh,Finset.sum_const,smul_eq_mul]
  ring

noncomputable def overlapExceptions (K E : Finset G) (δ : ℝ) : Finset G :=
  Finset.univ.filter (fun x => δ*K.card < overlapCount K E x)

lemma overlapExceptions_card (K E : Finset G) (hK : K.Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    ((overlapExceptions K E δ).card:ℝ) ≤ E.card/δ := by
  have hKp : (0:ℝ) < K.card := by exact_mod_cast Finset.card_pos.mpr hK
  have hs : ((overlapExceptions K E δ).card:ℝ)*(δ*K.card) ≤
      ∑ x : G, (overlapCount K E x:ℝ) := by
    have h1 : ∑ x ∈ overlapExceptions K E δ, δ*K.card ≤
        ∑ x ∈ overlapExceptions K E δ, (overlapCount K E x:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      exact (Finset.mem_filter.mp hx).2.le
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ (overlapExceptions K E δ))
      (fun x _ _ => (Nat.cast_nonneg (overlapCount K E x): (0:ℝ)≤_))
    simpa only [Finset.sum_const,nsmul_eq_mul] using h1.trans h2
  have he : (∑ x : G, (overlapCount K E x:ℝ)) = (K.card:ℝ)*E.card := by
    exact_mod_cast overlapCount_sum K E
  rw [he] at hs
  apply (le_div_iff₀ hδ).mpr
  nlinarith only [hs,hKp]

lemma coverage_hit_lower (q : FinLaw G) (K E : Finset G) {τ δ : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 3/8) (hδ : 0 < δ) (hδ1 : δ ≤ 1/64)
    (hq : ∀ y ∉ E, (τ+4*δ)/(Fintype.card G:ℝ) ≤ q y)
    {x : G} (hx : x ∉ overlapExceptions K E δ) :
    (τ+2*δ)*(K.card:ℝ)/(Fintype.card G:ℝ) ≤ q.prob (fun y => x+y ∈ K) := by
  have hne := q.nonempty
  have hp : (0:ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hoc : (overlapCount K E x:ℝ) ≤ δ*K.card := by
    simpa only [overlapExceptions,Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hx
  let S := Finset.univ.filter (fun y : G => x+y ∈ K ∧ y ∉ E)
  have hcount : (S.card:ℝ)+(overlapCount K E x:ℝ) = K.card := by
    have ht : S.card+overlapCount K E x=K.card := by
      have hbase : (Finset.univ.filter (fun y : G => x+y ∈ K)).card = K.card := by
        simp only [Finset.card_filter]
        calc
          _ = ∑ y : G, if y ∈ K then (1:ℕ) else 0 :=
            Equiv.sum_comp (Equiv.addLeft x) (fun y => if y ∈ K then (1:ℕ) else 0)
          _ = K.card := by simp
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := Finset.univ.filter (fun y : G => x+y ∈ K)) (p := fun y => y ∈ E)
      have hE : ((Finset.univ.filter (fun y : G => x+y ∈ K)).filter (fun y => y ∈ E)).card =
          overlapCount K E x := by
        unfold overlapCount
        congr 1
        ext y
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        tauto
      have hS : (Finset.univ.filter (fun y : G => x+y ∈ K)).filter (fun y => y ∉ E) = S := by
        ext y
        simp [S]
      rw [hE,hS,hbase] at hsplit
      omega
    exact_mod_cast ht
  have h1 : (S.card:ℝ)*((τ+4*δ)/(Fintype.card G:ℝ)) ≤ ∑ y ∈ S, q y := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum (s := S)
      (fun y hy => hq y (Finset.mem_filter.mp hy).2.2)
  have h2 : (∑ y ∈ S, q y) ≤ q.prob (fun y => x+y ∈ K) := by
    have he : q.prob (fun y => x+y ∈ K) =
        ∑ y ∈ Finset.univ.filter (fun y : G => x+y ∈ K), q y := by
      simp only [FinLaw.prob,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : x+y ∈ K <;> simp only [hy,ite_true,ite_false]
    rw [he]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ y,(Finset.mem_filter.mp hy).2.1⟩
    · intro y _ _
      exact q.nonneg y
  have h3 : (τ+2*δ)*K.card ≤ S.card*(τ+4*δ) := by
    have hc : (0:ℝ) ≤ K.card := Nat.cast_nonneg _
    have hd : τ+2*δ ≤ (1-δ)*(τ+4*δ) := by nlinarith only [hτ1,hδ1,hδ]
    have hm := mul_le_mul_of_nonneg_right hd hc
    have hs : (1-δ)*(K.card:ℝ) ≤ S.card := by linarith only [hcount,hoc]
    have ht := mul_le_mul_of_nonneg_right hs (by positivity : (0:ℝ) ≤ τ+4*δ)
    linarith only [hm,ht]
  calc
    _ ≤ (S.card:ℝ)*((τ+4*δ)/(Fintype.card G:ℝ)) := by
      simpa only [mul_div_assoc] using (div_le_div_iff_of_pos_right hp).mpr h3
    _ ≤ _ := h1.trans h2

noncomputable def coverageList (K : Finset G) (n : ℕ) (τ δ : ℝ) (h : Fin n → G) : Finset G :=
  Finset.univ.filter (fun x =>
    (∑ i : Fin n, if x+h i ∈ K then (1:ℝ) else 0) ≤
      n*(τ+δ)*K.card/(Fintype.card G:ℝ))

theorem coverageList_tail (q : FinLaw G) (K E : Finset G) (hK : K.Nonempty)
    {τ δ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 3/8) (hδ : 0 < δ) (hδ1 : δ ≤ 1/64)
    (hq : ∀ y ∉ E, (τ+4*δ)/(Fintype.card G:ℝ) ≤ q y) (n : ℕ) :
    (q.iid n).prob (fun h => ¬ coverageList K n τ δ h ⊆ overlapExceptions K E δ) ≤
      (Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*δ^2*K.card/(2*(Fintype.card G:ℝ))) := by
  have hne := q.nonempty
  have hp : (0:ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hKp : (0:ℝ) < K.card := by exact_mod_cast Finset.card_pos.mpr hK
  let μ := (τ+2*δ)*(K.card:ℝ)/(Fintype.card G:ℝ)
  let d := δ*(K.card:ℝ)/(Fintype.card G:ℝ)
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hx (x : G) : (q.iid n).prob (fun h => x ∈ coverageList K n τ δ h ∧
      x ∉ overlapExceptions K E δ) ≤
      Real.exp (-(n:ℝ)*δ^2*K.card/(2*(Fintype.card G:ℝ))) := by
    by_cases he : x ∈ overlapExceptions K E δ
    · simp only [he,not_true_eq_false,and_false,FinLaw.prob,ite_false,Finset.sum_const_zero]
      exact (Real.exp_pos _).le
    · have hh := q.iid_lower_tail (fun y => x+y ∈ K) n hμ hd
        (coverage_hit_lower q K E hτ hτ1 hδ hδ1 hq he)
      have hth : (n:ℝ)*(μ-d) = (n:ℝ)*(τ+δ)*K.card/(Fintype.card G:ℝ) := by
        dsimp [μ,d]
        ring
      rw [hth] at hh
      have hm : (q.iid n).prob (fun h => x ∈ coverageList K n τ δ h ∧
          x ∉ overlapExceptions K E δ) ≤
          (q.iid n).prob (fun h =>
            (∑ i : Fin n, if x+h i ∈ K then (1:ℝ) else 0) ≤
              n*(τ+δ)*K.card/(Fintype.card G:ℝ)) := by
        apply FinLaw.prob_mono
        intro h hh
        exact (Finset.mem_filter.mp hh.1).2
      apply (hm.trans (by
        convert! hh using 1
        congr 1
        funext v
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : x+v i ∈ K <;> simp only [hi,ite_true,ite_false])).trans
      apply Real.exp_le_exp.mpr
      have heq : d^2/μ = δ^2*(K.card:ℝ)/((τ+2*δ)*(Fintype.card G:ℝ)) := by
        dsimp [d,μ]
        field_simp
      have ht : 0 < τ+2*δ := by positivity
      have ht1 : τ+2*δ ≤ 1 := by linarith only [hτ1,hδ1]
      have hratio : δ^2*(K.card:ℝ)/(Fintype.card G:ℝ) ≤ d^2/μ := by
        rw [heq]
        apply div_le_div_of_nonneg_left (by positivity) (mul_pos ht hp)
        exact mul_le_of_le_one_left hp.le ht1
      have hmul := mul_le_mul_of_nonneg_left hratio (show (0:ℝ) ≤ n/2 by positivity)
      calc
        _ = -((n:ℝ)/2*(d^2/μ)) := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
        _ ≤ -((n:ℝ)/2*(δ^2*(K.card:ℝ)/(Fintype.card G:ℝ))) := neg_le_neg hmul
        _ = _ := by ring
  have hu := (q.iid n).prob_exists_le_sum (fun x h => x ∈ coverageList K n τ δ h ∧
    x ∉ overlapExceptions K E δ)
  have hm : (q.iid n).prob (fun h => ¬ coverageList K n τ δ h ⊆ overlapExceptions K E δ) ≤
      (q.iid n).prob (fun h => ∃ x, x ∈ coverageList K n τ δ h ∧ x ∉ overlapExceptions K E δ) := by
    apply FinLaw.prob_mono
    intro h hh
    by_contra hn
    apply hh
    intro x hx
    by_contra he
    exact hn ⟨x,hx,he⟩
  apply (hm.trans hu).trans
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
    Finset.sum_le_sum (s := Finset.univ) (fun x _ => hx x)

end

namespace FinLaw

section
open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω] [Fintype α]

lemma prod_ite_forall {ι : Type uIota} [Fintype ι] (P : ι → Prop) (f : ι → ℝ) :
    (∏ i, if P i then f i else 0) = if ∀ i, P i then ∏ i, f i else 0 := by
  by_cases h : ∀ i, P i
  · simp [h]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i,hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma iid_map (p : FinLaw Ω) (f : Ω → α) (n : ℕ) :
    (p.iid n).map (fun x i => f (x i)) = (p.map f).iid n := by
  ext y
  simp only [map_mass,iid_mass]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [prod_ite_forall]
  congr 1
  exact propext funext_iff

lemma iid_prob_forall (p : FinLaw Ω) (E : Ω → Prop) (n : ℕ) :
    (p.iid n).prob (fun x => ∀ i, E (x i)) = (p.prob E)^n := by
  simp only [prob,iid_mass]
  calc
    _ = ∑ x : Fin n → Ω, ∏ i, if E (x i) then p (x i) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      have h := prod_ite_forall (fun i => E (x i)) (fun i => p (x i))
      by_cases hh : ∀ i, E (x i) <;> simpa only [hh,ite_true,ite_false] using h.symm
    _ = _ := by
      rw [← Fintype.prod_sum (fun (_ : Fin n) (ω : Ω) => if E ω then p ω else (0:ℝ))]
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma iid_prob_implies (p : FinLaw Ω) (E F : Ω → Prop) (n : ℕ)
    (h : ∀ x, E x → ¬ F x) :
    (p.iid n).prob (fun x => ∀ i, E (x i)) ≤ (1-p.prob F)^n := by
  rw [← p.prob_compl F,← p.iid_prob_forall]
  exact (p.iid n).prob_mono (fun x hx i => h _ (hx i))

lemma iid_survival_exp (p : FinLaw Ω) (E : Ω → Prop) (n : ℕ) {c : ℝ}
    (hp : c ≤ 1-p.prob E) :
    (p.iid n).prob (fun x => ∀ i, E (x i)) ≤ Real.exp (-(n:ℝ)*c) := by
  have hbase : p.prob E ≤ Real.exp (-c) := by
    have h := Real.add_one_le_exp (-c)
    linarith only [hp,h]
  rw [iid_prob_forall]
  calc
    _ ≤ (Real.exp (-c))^n := pow_le_pow_left₀ (p.prob_nonneg E) hbase n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma expect_map (p : FinLaw Ω) (f : Ω → α) (g : α → ℝ) :
    (∑ a, p.map f a*g a) = ∑ ω, p ω*g (f ω) := by
  simp only [map_mass,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [ite_mul,zero_mul]
  simp

lemma joint_expect_snd (p : FinLaw Ω) (q : Ω → FinLaw α) (f : Ω → α → ℝ) :
    (∑ v, p.joint q v*f v.1 v.2) = ∑ ω, p ω*(∑ a, q ω a*f ω a) := by
  simp only [Fintype.sum_prod_type,joint_mass,Finset.mul_sum,mul_assoc]

lemma prob_map_true (p : FinLaw Ω) (E : Ω → Prop) :
    p.map (fun ω => decide (E ω)) true = p.prob E := by
  simp only [map_mass,decide_eq_true_eq,prob]

lemma prob_le_of_expect (p : FinLaw Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) {c t : ℝ} (ht : 0 < t)
    (hc : (∑ ω, p ω*f ω) ≤ c) :
    1-c/t ≤ p.prob (fun ω => f ω ≤ t) := by
  have h := (p.prob_le_expect_div f hf ht).trans ((div_le_div_iff_of_pos_right ht).mpr hc)
  have he := p.prob_compl (fun ω => f ω ≤ t)
  simp only [not_le] at he
  linarith only [h,he]

end

open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω] [Fintype α] [Fintype β]

lemma H_sub_H_of_agree (p : FinLaw Ω) (X Y : Ω → α) (E : Ω → Bool)
    (hE : ∀ ω, p ω ≠ 0 → E ω = true → X ω=Y ω) :
    p.H X-p.H Y ≤ Real.binEntropy (p.map E true)+
      (1-p.map E true)*Real.log (Fintype.card α) := by
  have h := p.short_list X Y (fun y => {y}) E (b := 1) le_rfl (by
    intro ω hp he
    simp only [Finset.mem_singleton,Finset.card_singleton,Nat.cast_one,le_refl,and_true]
    exact hE ω hp he)
  rw [Real.log_one,mul_zero,add_zero] at h
  have hc := p.H_le_condH_add X Y
  linarith only [h,hc]

lemma condH_sub_condH_of_agree (p : FinLaw Ω) (X X' : Ω → α) (O O' : Ω → β)
    (E : Ω → Bool) (hE : ∀ ω, p ω ≠ 0 → E ω=true → X ω=X' ω ∧ O ω=O' ω) :
    p.condH X O-p.condH X' O' ≤ 2*Real.binEntropy (p.map E true)+
      (1-p.map E true)*(Real.log (Fintype.card α)+2*Real.log (Fintype.card β)) := by
  have h1 := p.H_sub_H_of_agree (fun ω => (X ω,O ω)) (fun ω => (X' ω,O' ω)) E
    (fun ω hp he => Prod.ext (hE ω hp he).1 (hE ω hp he).2)
  have h2 := p.H_sub_H_of_agree O' O E (fun ω hp he => (hE ω hp he).2.symm)
  have hn := p.nonempty
  have ha : Nonempty α := ⟨X (Classical.arbitrary Ω)⟩
  have hb : Nonempty β := ⟨O (Classical.arbitrary Ω)⟩
  have hca : (Fintype.card α:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcb : (Fintype.card β:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Fintype.card_prod,Nat.cast_mul,Real.log_mul hca hcb] at h1
  unfold condH
  linarith only [h1,h2]

lemma binEntropy_le_log_inverse {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    Real.binEntropy a ≤ a*(1-Real.log a) := by
  have h : Real.negMulLog (1-a) ≤ a := by
    by_cases hz : 1-a=0
    · simp only [hz,Real.negMulLog_zero]
      exact ha.le
    · have hp : 0 < 1-a := lt_of_le_of_ne (by linarith) (Ne.symm hz)
      have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
      rw [Real.log_inv] at hh
      have hm := mul_le_mul_of_nonneg_left hh hp.le
      rw [mul_sub,mul_inv_cancel₀ hz,mul_one] at hm
      unfold Real.negMulLog
      linarith only [hm]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  dsimp only [Real.negMulLog] at h ⊢
  linarith only [h]

lemma binEntropy_sum_le {ι : Type uIota} [Fintype ι] (w : FinLaw ι) (a : ι → ℝ)
    (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1) :
    (∑ i, w i*Real.binEntropy (a i)) ≤ Real.binEntropy (∑ i, w i*a i) := by
  exact Real.strictConcave_binEntropy.concaveOn.le_map_sum (fun i _ => w.nonneg i) w.sum_one (fun i _ => ha i)

end FinLaw

open scoped BigOperators Classical
namespace FinLaw
variable {Ω : Type uOmega} {Γ : Type uCapitalGamma} {G : Type uGroup} [Fintype Ω] [Fintype Γ] [Fintype G] [AddCommGroup G]

omit [AddCommGroup G] in
lemma prob_mem_finset (p : FinLaw G) (K : Finset G) :
    p.prob (fun x => x ∈ K) = ∑ x ∈ K, p x := by
  unfold prob
  calc
    _ = ∑ x ∈ K, if x ∈ K then p x else 0 := by
      symm
      convert! Finset.sum_subset (Finset.subset_univ K)
        (f := fun x => if x ∈ K then p x else (0:ℝ))
        (fun x _ hx => ite_eq_right hx) using 1
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x∈K <;> simp only [hx,ite_true,ite_false]
    _ = _ := Finset.sum_congr rfl (fun x hx => ite_eq_left hx)

lemma joint_prob_le_bad_add (p : FinLaw Ω) (q : Ω → FinLaw Γ)
    (Bad : Ω → Prop) (E : Ω × Γ → Prop) {ε : ℝ} (hε : 0 ≤ ε)
    (hg : ∀ ω, ¬ Bad ω → (q ω).prob (fun a => E (ω,a)) ≤ ε) :
    (p.joint q).prob E ≤ p.prob Bad+ε := by
  rw [prob_joint]
  have h (ω : Ω) : (q ω).prob (fun a => E (ω,a)) ≤ (if Bad ω then 1 else 0)+ε := by
    by_cases hb : Bad ω
    · simpa only [hb,ite_true] using (q ω).prob_le_one (fun a => E (ω,a)) |>.trans (by linarith only [hε])
    · simpa only [hb,ite_false,zero_add] using hg ω hb
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
    mul_le_mul_of_nonneg_left (h ω) (p.nonneg ω))
  convert! hh using 1
  simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,p.sum_one,one_mul,prob]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

omit [Fintype G] in

lemma iid_true_hit_expect (p : FinLaw Ω) (q : Ω → FinLaw Γ)
    (Y : Ω → G) (h : Γ → G) (K : Finset G) (n : ℕ) :
    (∑ v, p.joint (fun ω => (q ω).iid n) v *
      (∑ i : Fin n, if Y v.1+h (v.2 i) ∈ K then (1:ℝ) else 0)) =
      n*(p.joint q).prob (fun v => Y v.1+h v.2 ∈ K) := by
  rw [joint_expect_snd p (fun ω => (q ω).iid n)
    (fun ω v => ∑ i : Fin n, if Y ω+h (v i) ∈ K then (1:ℝ) else 0)]
  have he (i : Fin n) (ω : Ω) :
      (∑ v, (q ω).iid n v*(if Y ω+h (v i) ∈ K then (1:ℝ) else 0)) =
        (q ω).prob (fun a => Y ω+h a ∈ K) := by
    rw [← expect_map ((q ω).iid n) (fun v => v i) (fun a => if Y ω+h a ∈ K then (1:ℝ) else 0),
      iid_map_eval]
    unfold prob
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  have hh (ω : Ω) :
      (∑ v, (q ω).iid n v*(∑ i : Fin n, if Y ω+h (v i) ∈ K then (1:ℝ) else 0)) =
        n*(q ω).prob (fun a => Y ω+h a ∈ K) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [hh,mul_left_comm (p _) (n:ℝ)]
  rw [← Finset.mul_sum,prob_joint p q (fun v => Y v.1+h v.2∈K)]

lemma true_coverageList_probability (p : FinLaw Ω) (q : Ω → FinLaw Γ)
    (Y : Ω → G) (h : Γ → G) (K : Finset G) (hK : K.Nonempty)
    {τ δ : ℝ} (hτ : 0 ≤ τ) (hδ : 0 < δ) {n : ℕ} (hn : 0 < n)
    (hp : (p.joint q).prob (fun v => Y v.1+h v.2 ∈ K) ≤
      τ*K.card/(Fintype.card G:ℝ)) :
    δ/(τ+δ) ≤ (p.joint (fun ω => (q ω).iid n)).prob
      (fun v => Y v.1 ∈ coverageList K n τ δ (fun i => h (v.2 i))) := by
  have hG : Nonempty G := ⟨Y (Classical.choice p.nonempty)⟩
  have hcard : (0:ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hkc : (0:ℝ) < K.card := by exact_mod_cast Finset.card_pos.mpr hK
  have hnc : (0:ℝ) < n := by exact_mod_cast hn
  have htd : 0 < τ+δ := by linarith
  have hb : (∑ v, p.joint (fun ω => (q ω).iid n) v *
      (∑ i : Fin n, if Y v.1+h (v.2 i) ∈ K then (1:ℝ) else 0)) ≤
        n*(τ*K.card/(Fintype.card G:ℝ)) := by
    rw [iid_true_hit_expect]
    exact mul_le_mul_of_nonneg_left hp hnc.le
  have hh := (p.joint (fun ω => (q ω).iid n)).prob_le_of_expect
    (fun v => ∑ i : Fin n, if Y v.1+h (v.2 i) ∈ K then (1:ℝ) else 0)
    (fun _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
    (t := n*(τ+δ)*K.card/(Fintype.card G:ℝ)) (by positivity) hb
  have he : 1-(n*(τ*K.card/(Fintype.card G:ℝ)))/(n*(τ+δ)*K.card/(Fintype.card G:ℝ)) =
      δ/(τ+δ) := by field_simp; ring
  rw [he] at hh
  simpa only [coverageList,Finset.mem_filter,Finset.mem_univ,true_and] using hh

lemma coverageList_size_probability (p : FinLaw Ω) (q : Ω → FinLaw Γ)
    (h : Γ → G) (K : Finset G) (hK : K.Nonempty) (E : Ω → Finset G)
    (Bad : Ω → Prop) {τ δ ε b : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 3/8) (hδ : 0 < δ) (hδ1 : δ ≤ 1/64)
    (hε : 0 ≤ ε) (n : ℕ)
    (hq : ∀ ω, ¬ Bad ω → ∀ y ∉ E ω,
      (τ+4*δ)/(Fintype.card G:ℝ) ≤ (q ω).map h y)
    (hE : ∀ ω, ¬ Bad ω → ((E ω).card:ℝ)/δ ≤ b)
    (herr : (Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*δ^2*K.card/(2*(Fintype.card G:ℝ))) ≤ ε) :
    (p.joint (fun ω => (q ω).iid n)).prob (fun v =>
      b < ((coverageList K n τ δ (fun i => h (v.2 i))).card:ℝ)) ≤ p.prob Bad+ε := by
  apply joint_prob_le_bad_add p _ Bad _ hε
  intro ω hg
  have ha := (coverageList_tail ((q ω).map h) K (E ω) hK hτ hτ1 hδ hδ1 (hq ω hg) n).trans herr
  rw [← iid_map,prob_map] at ha
  apply (prob_mono _ ?_).trans ha
  intro x hx hs
  have hc := Finset.card_le_card hs
  have hcR : ((coverageList K n τ δ (fun i => h (x i))).card:ℝ) ≤
      ((overlapExceptions K (E ω) δ).card:ℝ) := by exact_mod_cast hc
  have hb := (overlapExceptions_card K (E ω) hK hδ).trans (hE ω hg)
  linarith only [hx,hcR,hb]

end FinLaw
end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat
open scoped BigOperators Classical
namespace FinLaw
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω] [Fintype α] [Fintype β]

lemma short_list_probability_deficit (p : FinLaw Ω) (X : Ω → α) (C : Ω → β)
    (L : β → Finset α) {b : ℝ} (hb : 1 ≤ b) :
    let a := p.prob (fun ω => X ω ∈ L (C ω) ∧ ((L (C ω)).card:ℝ) ≤ b)
    a*(Real.log (Fintype.card α)-Real.log b)-Real.binEntropy a ≤
      Real.log (Fintype.card α)-p.cHf X C := by
  dsimp only
  have hh := p.short_list_deficit X C L
    (fun ω => decide (X ω ∈ L (C ω) ∧ ((L (C ω)).card:ℝ) ≤ b)) hb
    (fun ω _ he => of_decide_eq_true he)
  have ha : (p.map (fun ω => decide (X ω ∈ L (C ω) ∧ ((L (C ω)).card:ℝ) ≤ b))) true =
      p.prob (fun ω => X ω ∈ L (C ω) ∧ ((L (C ω)).card:ℝ) ≤ b) := by
    simp only [map_mass,decide_eq_true_eq,prob]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> rfl
  rw [ha] at hh
  simpa only [condH,← Hf_eq_H,cHf] using hh

lemma average_deficit_lower {ι : Type uIota} [Fintype ι] (w : FinLaw ι)
    (a d : ι → ℝ) {a₀ v : ℝ} (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1)
    (ha₀ : 0 < a₀) (hav : a₀ ≤ ∑ i, w i*a i)
    (hv : 2*(1-Real.log a₀) ≤ v)
    (hdef : ∀ i, a i*v-Real.binEntropy (a i) ≤ d i) :
    a₀*v/2 ≤ ∑ i, w i*d i := by
  let A := ∑ i, w i*a i
  have hA : 0 < A := lt_of_lt_of_le ha₀ hav
  have hA1 : A ≤ 1 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (ha i).2 (w.nonneg i))
    simpa only [mul_one,w.sum_one] using hh
  have ha₀1 : a₀ ≤ 1 := hav.trans hA1
  have hl : Real.log a₀ ≤ Real.log A := Real.log_le_log ha₀ hav
  have hl0 : Real.log a₀ ≤ 0 := Real.log_nonpos ha₀.le ha₀1
  have hv0 : 0 ≤ v := by linarith only [hv,hl0]
  have hh := w.binEntropy_sum_le a ha
  have hp := binEntropy_le_log_inverse hA hA1
  have hdl := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hdef i) (w.nonneg i))
  rw [show (∑ i, w i*(a i*v-Real.binEntropy (a i))) =
      A*v-∑ i, w i*Real.binEntropy (a i) by
        simp only [mul_sub,Finset.sum_sub_distrib,← mul_assoc,← Finset.sum_mul,A]] at hdl
  have hlog := mul_le_mul_of_nonneg_left hl hA.le
  have hmult := mul_le_mul_of_nonneg_left hv hA.le
  have ham := mul_le_mul_of_nonneg_right hav hv0
  change (∑ i, w i*Real.binEntropy (a i)) ≤ Real.binEntropy A at hh
  linarith only [hdl,hh,hp,hlog,hmult,ham]

theorem shared_coverage_deficit {Γ : Type uCapitalGamma} {G : Type uGroup} [Fintype Γ] [Fintype G] [AddCommGroup G]
    (p : FinLaw Ω) (q : Ω → FinLaw Γ) (Y : Ω → G) (h : Γ → G)
    (K : Finset G) (hK : K.Nonempty) (E : Ω → Finset G) (Bad : Ω → Prop)
    {τ δ ε b : ℝ} {n : ℕ} (hn : 0<n)
    (hτ : 0≤τ) (hτ1 : τ≤3/8) (hδ : 0<δ) (hδ1 : δ≤1/64)
    (hε : 0≤ε) (hb : 1≤b)
    (hp : (p.joint q).prob (fun v => Y v.1+h v.2∈K) ≤ τ*K.card/(Fintype.card G:ℝ))
    (hq : ∀ ω, ¬ Bad ω → ∀ y ∉ E ω, (τ+4*δ)/(Fintype.card G:ℝ) ≤ (q ω).map h y)
    (hE : ∀ ω, ¬ Bad ω → ((E ω).card:ℝ)/δ≤b)
    (herr : (Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*δ^2*K.card/(2*(Fintype.card G:ℝ)))≤ε) :
    let P := p.joint (fun ω => (q ω).iid n)
    let L := fun v : Fin n → Γ => coverageList K n τ δ (fun i => h (v i))
    let a := P.prob (fun v => Y v.1 ∈ L v.2 ∧ ((L v.2).card:ℝ)≤b)
    δ/(τ+δ)-p.prob Bad-ε ≤ a ∧
      a*(Real.log (Fintype.card G)-Real.log b)-Real.binEntropy a ≤
        Real.log (Fintype.card G)-P.cHf (fun v => Y v.1) Prod.snd := by
  dsimp only
  constructor
  · have htrue := p.true_coverageList_probability q Y h K hK hτ hδ hn hp
    have hsize := p.coverageList_size_probability q h K hK E Bad hτ hτ1 hδ hδ1 hε n hq hE herr
    have hi := (p.joint (fun ω => (q ω).iid n)).prob_inter_ge
      (fun v => Y v.1 ∈ coverageList K n τ δ (fun i => h (v.2 i)))
      (fun v => ((coverageList K n τ δ (fun i => h (v.2 i))).card:ℝ)≤b)
    simp only [not_le] at hi
    linarith only [htrue,hsize,hi]
  · exact short_list_probability_deficit (p.joint (fun ω => (q ω).iid n))
      (fun v => Y v.1) Prod.snd
      (fun v => coverageList K n τ δ (fun i => h (v i))) hb

end FinLaw

lemma perm_expect_apply {ι : Type uIota} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (i : ι) :
    (𝔼 π : Equiv.Perm ι, f (π i)) = 𝔼 j, f j := by
  let : Nonempty ι := ⟨i⟩
  calc
    _ = 𝔼 j : ι, 𝔼 π : Equiv.Perm ι, f (π j) := by
      rw [show (fun j : ι => 𝔼 π : Equiv.Perm ι, f (π j)) =
        (fun _ => 𝔼 π : Equiv.Perm ι, f (π i)) by
          funext j; exact perm_expect_exchange f j i]
      simp only [Fintype.expect_const]
    _ = 𝔼 π : Equiv.Perm ι, 𝔼 j : ι, f (π j) := Finset.expect_comm _ _ _
    _ = _ := by
      have he (π : Equiv.Perm ι) : (𝔼 j, f (π j)) = 𝔼 j, f j :=
        Fintype.expect_equiv π _ _ (fun _ => rfl)
      simp only [he,Fintype.expect_const]

namespace FinLaw
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω] {k : ℕ}

lemma Hf_sub_le_cHf (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.Hf X-p.Hf Y ≤ p.cHf X Y := by
  have h := p.Hf_pair_ge_snd Y X
  rw [p.Hf_pair_comm Y X] at h
  exact sub_le_sub_right h _

lemma orderedEntropy_conditioning (p : FinLaw Ω) (X : Ω → Fin k → α)
    (C : Ω → β) {b : ℕ} (hb : b ≤ k) :
    p.orderedEntropy X b-p.Hf C ≤
      b*(𝔼 i : Fin k, p.cHf (fun ω => X ω i) C) := by
  have hh (π : Equiv.Perm (Fin k)) :
      p.Hf (prefixVar X π b)-p.Hf C ≤
        ∑ i : Fin b, p.cHf (fun ω => X ω (π ⟨i.val,lt_of_lt_of_le i.isLt hb⟩)) C := by
    apply (p.Hf_sub_le_cHf _ C).trans
    apply (p.cHf_le_of_determined _
      (fun ω (i : Fin b) => X ω (π ⟨i.val,lt_of_lt_of_le i.isLt hb⟩)) C ?_).trans
      (p.cHf_fintype_subadd _ C)
    intro ω ν hx _
    funext i
    by_cases hi : i.val<b
    · simpa only [prefixVar,hi,ite_eq_left] using congrArg some (congrFun hx ⟨i.val,hi⟩)
    · simp only [prefixVar,hi,ite_false]
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun π _ => hh π)
  have he (i : Fin b) :
      (𝔼 π : Equiv.Perm (Fin k), p.cHf (fun ω => X ω (π ⟨i.val,lt_of_lt_of_le i.isLt hb⟩)) C) =
        𝔼 j : Fin k, p.cHf (fun ω => X ω j) C :=
    perm_expect_apply (fun j => p.cHf (fun ω => X ω j) C) _
  simpa only [orderedEntropy,Finset.expect_sub_distrib,Fintype.expect_const,
    Finset.expect_sum_comm,he,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] using hav

lemma signedEntropy_conditioning (p : FinLaw Ω) (X : (Fin k → Bool) → Ω → Fin k → α)
    (C : Ω → β) {b : ℕ} (hb : b ≤ k) :
    p.signedEntropy X b-p.Hf C ≤
      b*(𝔼 σ : Fin k → Bool, 𝔼 i : Fin k, p.cHf (fun ω => X σ ω i) C) := by
  have h := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    p.orderedEntropy_conditioning (X σ) C hb)
  simpa only [signedEntropy,Finset.expect_sub_distrib,Fintype.expect_const,
    Finset.mul_expect] using h

end FinLaw

theorem SplitSieve.coverage_conditioning {Ω : Type uOmega} {β : Type uBeta} [Fintype Ω]
    (s : SplitSieve) (p : FinLaw Ω) (Y : Ω → GaussianInt) (C : Ω → β)
    {b : ℕ} (hb : b ≤ s.primes.card) :
    s.pointEntropy p Y b-p.Hf C ≤
      b*(𝔼 σ : Fin s.primes.card → Bool, 𝔼 i : Fin s.primes.card,
        p.cHf (fun ω => s.residueVector σ (Y ω) i) C) :=
  p.signedEntropy_conditioning _ C hb

namespace FinLaw

section

theorem backward_coverage_step {Ω : Type uOmega} {Γ : Type uCapitalGamma} {ι : Type uIota} [Fintype Ω] [Fintype Γ] [Fintype ι]
    (G : ι → Type uGroup) [∀ i, Fintype (G i)] [∀ i, AddCommGroup (G i)]
    (w : FinLaw ι) (p : FinLaw Ω) (q : Ω → FinLaw Γ)
    (Y : (i : ι) → Ω → G i) (h : (i : ι) → Γ → G i)
    (Bad₀ : ι → Prop) (Bad₁ : ι → Ω → Prop)
    (K : (i : ι) → Finset (G i)) (E : (i : ι) → Ω → Finset (G i))
    (b : ι → ℝ) {τ δ ε η η' e v : ℝ} {n : ℕ}
    (hn : 0 < n) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 3/8)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/64) (hε : 0 ≤ ε) (hη : 0 < η)
    (hnext : ∑ i, w i*p.prob (Bad₁ i) ≤ η')
    (hsmall : η'+ε ≤ η*δ/2)
    (hscale : 2*(1-Real.log (η*δ/2)) ≤ v)
    (hgap : e < η*δ*v/4)
    (hdata : (∑ i, w i*(Real.log (Fintype.card (G i))-
      (p.joint (fun ω => (q ω).iid n)).cHf (fun x => Y i x.1) Prod.snd)) ≤ e)
    (hK : ∀ i, Bad₀ i → (K i).Nonempty)
    (hb : ∀ i, Bad₀ i → 1 ≤ b i)
    (hv : ∀ i, Bad₀ i → v ≤ Real.log (Fintype.card (G i))-Real.log (b i))
    (hp : ∀ i, Bad₀ i → (p.joint q).prob (fun x => Y i x.1+h i x.2 ∈ K i) ≤
      τ*(K i).card/(Fintype.card (G i):ℝ))
    (hq : ∀ i, Bad₀ i → ∀ ω, ¬Bad₁ i ω → ∀ y ∉ E i ω,
      (τ+4*δ)/(Fintype.card (G i):ℝ) ≤ (q ω).map (h i) y)
    (hE : ∀ i, Bad₀ i → ∀ ω, ¬Bad₁ i ω → ((E i ω).card:ℝ)/δ ≤ b i)
    (herr : ∀ i, Bad₀ i → (Fintype.card (G i):ℝ)*
      Real.exp (-(n:ℝ)*δ^2*(K i).card/(2*(Fintype.card (G i):ℝ))) ≤ ε) :
    w.prob Bad₀ ≤ η := by
  let P := p.joint (fun ω => (q ω).iid n)
  let L := fun i (x : Fin n → Γ) => coverageList (K i) n τ δ (fun j => h i (x j))
  let a := fun i => if Bad₀ i then P.prob
    (fun x => Y i x.1 ∈ L i x.2 ∧ ((L i x.2).card:ℝ) ≤ b i) else 0
  let d := fun i => Real.log (Fintype.card (G i))-P.cHf (fun x => Y i x.1) Prod.snd
  have hd (i : ι) : 0 ≤ d i := by
    exact sub_nonneg.mpr ((P.cHf_le_Hf _ _).trans (P.Hf_le_log_card_type _))
  have ha (i : ι) : a i ∈ Set.Icc (0:ℝ) 1 := by
    dsimp only [a]
    split_ifs
    · exact ⟨P.prob_nonneg _,P.prob_le_one _⟩
    · norm_num
  have hstep (i : ι) (hi : Bad₀ i) :
      δ-p.prob (Bad₁ i)-ε ≤ a i ∧ a i*v-Real.binEntropy (a i) ≤ d i := by
    have hh := shared_coverage_deficit p q (Y i) (h i) (K i) (hK i hi) (E i) (Bad₁ i)
      hn hτ hτ1 hδ hδ1 hε (hb i hi) (hp i hi) (hq i hi) (hE i hi) (herr i hi)
    dsimp only at hh
    have hh' : δ/(τ+δ)-p.prob (Bad₁ i)-ε ≤ a i ∧
        a i*(Real.log (Fintype.card (G i))-Real.log (b i))-Real.binEntropy (a i) ≤ d i := by
      simpa only [a,hi,ite_eq_left,P,L,d] using hh
    constructor
    · have htd : 0 < τ+δ := by linarith only [hτ,hδ]
      have htd1 : τ+δ ≤ 1 := by linarith only [hτ1,hδ1]
      have hfrac : δ ≤ δ/(τ+δ) := (le_div_iff₀ htd).mpr (by nlinarith only [htd1,hδ])
      linarith only [hh'.1,hfrac]
    · have hm := mul_le_mul_of_nonneg_left (hv i hi) (ha i).1
      linarith only [hh'.2,hm]
  have hl (i : ι) : δ*(if Bad₀ i then (1:ℝ) else 0)-p.prob (Bad₁ i)-ε ≤ a i := by
    by_cases hi : Bad₀ i
    · simpa only [hi,ite_true,mul_one] using (hstep i hi).1
    · simp only [hi,ite_false,mul_zero,a]
      linarith only [p.prob_nonneg (Bad₁ i),hε]
  have hdef (i : ι) : a i*v-Real.binEntropy (a i) ≤ d i := by
    by_cases hi : Bad₀ i
    · exact (hstep i hi).2
    · simpa only [a,hi,ite_false,Real.binEntropy_zero,zero_mul,sub_zero] using hd i
  by_contra hc
  have hθη : η < w.prob Bad₀ := lt_of_not_ge hc
  have hlavg := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hl i) (w.nonneg i))
  have heq : (∑ i, w i*(δ*(if Bad₀ i then (1:ℝ) else 0)-p.prob (Bad₁ i)-ε)) =
      δ*w.prob Bad₀-(∑ i, w i*p.prob (Bad₁ i))-ε := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,w.sum_one,one_mul,prob,
      Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [heq] at hlavg
  have hav : η*δ/2 ≤ ∑ i, w i*a i := by
    have hm := mul_le_mul_of_nonneg_left hθη.le hδ.le
    linarith only [hlavg,hm,hnext,hsmall]
  have hbnd := average_deficit_lower w a d ha (by positivity : 0 < η*δ/2) hav hscale hdef
  change (∑ i, w i*d i) ≤ e at hdata
  linarith only [hbnd,hdata,hgap]

variable {Ω : Type uOmega} {G : Type uGroup} [Fintype Ω] [Fintype G]

theorem low_mass_average {ι : Type uIota} [Fintype ι]
    (G : ι → Type uGroup) [∀ i, Fintype (G i)]
    (w : FinLaw ι) (p : (i : ι) → FinLaw (G i))
    (K : (i : ι) → Finset (G i)) (Bad : ι → Prop) {b e : ℝ}
    (hb : 0 < b)
    (hK : ∀ i, ∀ x ∈ K i, p i x ≤ (3/8:ℝ)/(Fintype.card (G i):ℝ))
    (hbad : ∀ i, Bad i → b ≤ ((K i).card:ℝ)/(8*(Fintype.card (G i):ℝ)))
    (hdef : (∑ i, w i*(Real.log (Fintype.card (G i))-(p i).entropy)) ≤ e) :
    w.prob Bad ≤ e/b := by
  have h (i : ι) : b*(if Bad i then (1:ℝ) else 0) ≤
      Real.log (Fintype.card (G i))-(p i).entropy := by
    by_cases hi : Bad i
    · simp only [hi,ite_true,mul_one]
      exact (hbad i hi).trans ((p i).low_mass_deficit (K i) (by
        intro x hx
        convert hK i x hx using 1; ring))
    · simp only [hi,ite_false,mul_zero]
      exact sub_nonneg.mpr (p i).entropy_le_log_card
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (h i) (w.nonneg i))
  have he : (∑ i, w i*(b*(if Bad i then (1:ℝ) else 0)))=b*w.prob Bad := by
    rw [prob,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [he] at hs
  apply (le_div_iff₀ hb).mpr
  linarith only [hs,hdef]

end

variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω] [Fintype α] [Fintype β]

lemma uniform_map_perm [Nonempty Ω] (e : Equiv.Perm Ω) : (uniform Ω).map e = uniform Ω := by
  ext x
  rw [map_equiv_mass]
  rfl

lemma prob_uniform (E : Ω → Prop) [Nonempty Ω] :
    (uniform Ω).prob E = ((Finset.univ.filter E).card:ℝ)/(Fintype.card Ω:ℝ) := by
  simp only [prob,uniform_mass,div_eq_mul_inv]
  rw [← Finset.sum_boole]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

lemma uniform_no_wrap (n a : ℕ) (ha : a ≤ n+1) :
    (uniform (Fin (n+1))).prob (fun i => i.val+a<n+1) = 1-(a:ℝ)/(n+1) := by
  rw [prob_uniform]
  have he : (Finset.univ.filter (fun i : Fin (n+1) => i.val+a<n+1)) =
      Finset.univ.filter (fun i : Fin (n+1) => i.val<n+1-a) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  have hcard : (Finset.univ.filter (fun i : Fin (n+1) => i.val+a<n+1)).card = n+1-a := by
    rw [he,Fin.card_filter_val_lt,Nat.min_eq_right (by omega)]
  calc
    _ = ((n+1-a:ℕ):ℝ)/(n+1) := by
      congr 1
      · convert! congrArg (fun k : ℕ => (k:ℝ)) hcard using 1
        congr 2
        ext i
        simp
      · simp
    _ = _ := by
      rw [Nat.cast_sub ha,Nat.cast_add,Nat.cast_one]
      field_simp

lemma joint_perm_second (p : FinLaw Ω) {Γ : Type uCapitalGamma} [Fintype Γ] [Nonempty Γ]
    (e : Equiv.Perm Γ) :
    (p.joint (fun _ => uniform Γ)).map (fun v => (v.1,e v.2)) = p.joint (fun _ => uniform Γ) := by
  have h := joint_map_fiber p (fun _ => uniform Γ) (fun _ v => e v)
  simpa only [uniform_map_perm] using h

lemma smoothing_prob (p : FinLaw Ω) (t : Ω → ℕ) (n a : ℕ) (ha : a≤n)
    (E : ℕ → Prop) :
    (p.joint (fun _ => uniform (Fin (n+1)))).prob (fun v => E (t v.1+v.2.val)) ≤
      (p.joint (fun _ => uniform (Fin (n+1)))).prob (fun v => E (t v.1+v.2.val+a))+
        (a:ℝ)/(n+1) := by
  let e : Equiv.Perm (Fin (n+1)) := Equiv.addRight ⟨a,by omega⟩
  let P := p.joint (fun _ => uniform (Fin (n+1)))
  have hprob : P.prob (fun v => E (t v.1+(e v.2).val)) =
      P.prob (fun v => E (t v.1+v.2.val)) := by
    have hh := congrArg (fun Q : FinLaw (Ω × Fin (n+1)) => Q.prob
      (fun v => E (t v.1+v.2.val))) (p.joint_perm_second e)
    simpa only [prob_map] using hh
  have hgood : P.prob (fun v => v.2.val+a<n+1) = 1-(a:ℝ)/(n+1) := by
    rw [prob_joint]
    simp only [uniform_no_wrap n a (by omega),← Finset.sum_mul,p.sum_one,one_mul]
  have hE : P.prob (fun v => E (t v.1+(e v.2).val) ∧ v.2.val+a<n+1) ≤
      P.prob (fun v => E (t v.1+v.2.val+a)) := by
    apply P.prob_mono
    intro v hv
    have he : (e v.2).val = v.2.val+a := by
      change (v.2+(⟨a,by omega⟩ : Fin (n+1))).val = _
      exact Fin.val_add_eq_of_add_lt hv.2
    simpa only [he,Nat.add_assoc] using hv.1
  have hh := P.prob_inter_ge (fun v => E (t v.1+(e v.2).val)) (fun v => v.2.val+a<n+1)
  have hc := P.prob_compl (fun v => v.2.val+a<n+1)
  rw [hgood] at hc
  rw [hprob] at hh
  linarith only [hE,hh,hc]

lemma smoothing_condH (p : FinLaw Ω) (t : Ω → ℕ) (n a : ℕ) (ha : a≤n)
    (X : ℕ → α) (C : ℕ → β) :
    (p.joint (fun _ => uniform (Fin (n+1)))).condH
      (fun v => X (t v.1+v.2.val+a)) (fun v => C (t v.1+v.2.val+a)) ≤
    (p.joint (fun _ => uniform (Fin (n+1)))).condH
      (fun v => X (t v.1+v.2.val)) (fun v => C (t v.1+v.2.val)) +
      2*Real.binEntropy ((a:ℝ)/(n+1))+
        ((a:ℝ)/(n+1))*(Real.log (Fintype.card α)+2*Real.log (Fintype.card β)) := by
  let e : Equiv.Perm (Fin (n+1)) := Equiv.addRight ⟨a,by omega⟩
  let P := p.joint (fun _ => uniform (Fin (n+1)))
  let good := fun v : Ω × Fin (n+1) => decide (v.2.val+a<n+1)
  have hm : P.map good true=1-(a:ℝ)/(n+1) := by
    have hh : P.map good true=P.prob (fun v => v.2.val+a<n+1) := by
      simp only [map_mass,good,prob,decide_eq_true_eq]
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> rfl
    rw [hh,prob_joint]
    simp only [uniform_no_wrap n a (by omega),
      ← Finset.sum_mul,p.sum_one,one_mul]
  have he : P.condH (fun v => X (t v.1+(e v.2).val)) (fun v => C (t v.1+(e v.2).val)) =
      P.condH (fun v => X (t v.1+v.2.val)) (fun v => C (t v.1+v.2.val)) := by
    have hh := congrArg (fun Q : FinLaw (Ω × Fin (n+1)) =>
      Q.condH (fun v => X (t v.1+v.2.val)) (fun v => C (t v.1+v.2.val))) (p.joint_perm_second e)
    simpa only [condH,H_map,Function.comp_def] using hh
  have h := P.condH_sub_condH_of_agree
    (fun v => X (t v.1+v.2.val+a)) (fun v => X (t v.1+(e v.2).val))
    (fun v => C (t v.1+v.2.val+a)) (fun v => C (t v.1+(e v.2).val)) good (by
      intro v _ hv
      have hlt : v.2.val+a<n+1 := of_decide_eq_true hv
      have hev : (e v.2).val=v.2.val+a := Fin.val_add_eq_of_add_lt hlt
      simp only [hev,Nat.add_assoc,and_self])
  rw [hm,he,Real.binEntropy_one_sub] at h
  linarith only [h]

end FinLaw
end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat

namespace FinLaw
open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} {Γ : Type uCapitalGamma} {G : Type uGroup} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype G]

lemma prob_and_split (p : FinLaw Ω) (A B : Ω → Prop) :
    p.prob (fun ω => A ω ∧ B ω)+p.prob (fun ω => A ω ∧ ¬B ω)=p.prob A := by
  simp only [prob,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases ha : A ω <;> by_cases hb : B ω <;> simp [ha,hb]

lemma prob_mix (p : FinLaw Ω) (q : Ω → FinLaw Γ) (E : Γ → Prop) :
    (p.mix q).prob E = ∑ ω, p ω*(q ω).prob E := by
  rw [← joint_map_snd,prob_map,prob_joint]

lemma posterior_unfavorable (p : FinLaw Ω) (C : Ω → α) (Bad : Ω → Prop) :
    (p.map C).prob (fun a => (1/2:ℝ)<(p.conditionOn C a).prob Bad) ≤ 2*p.prob Bad := by
  have h := (p.map C).prob_le_expect_div (fun a => (p.conditionOn C a).prob Bad)
    (fun a => (p.conditionOn C a).prob_nonneg _) (by norm_num : (0:ℝ)<1/2)
  rw [p.conditionOn_prob] at h
  linarith only [h]

lemma mixed_exception_card (p : FinLaw Ω) (Good : Ω → Prop) (E : Ω → Finset G)
    {e : ℝ} (he : 0≤e) (hE : ∀ ω, Good ω → ((E ω).card:ℝ)≤e)
    (hG : (1/2:ℝ)≤p.prob Good) :
    ((Finset.univ.filter (fun x : G =>
      p.prob (fun ω => Good ω ∧ x∉E ω)<1/4)).card:ℝ) ≤ 4*e := by
  let u := fun x => p.prob (fun ω => Good ω ∧ x∉E ω)
  let f := fun x => p.prob (fun ω => Good ω ∧ x∈E ω)
  let K := Finset.univ.filter (fun x : G => u x<1/4)
  have hsum : (∑ x : G, f x) ≤ e := by
    simp only [f,prob]
    rw [Finset.sum_comm]
    have hh (ω : Ω) : (∑ x : G, if Good ω ∧ x∈E ω then p ω else 0) ≤ p ω*e := by
      by_cases hg : Good ω
      · have hc : (∑ x : G, if Good ω ∧ x∈E ω then p ω else 0) = p ω*(E ω).card := by
          simp only [hg,true_and]
          calc
            _ = ∑ x : G, p ω*(if x∈E ω then (1:ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro x _
              split_ifs <;> simp
            _ = _ := by rw [← Finset.mul_sum]; simp
        rw [hc]
        exact mul_le_mul_of_nonneg_left (hE ω hg) (p.nonneg ω)
      · simp only [hg,false_and,ite_false,Finset.sum_const_zero]
        exact mul_nonneg (p.nonneg ω) he
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hh ω)
    simp only [← Finset.sum_mul,p.sum_one,one_mul] at ht
    refine le_trans (le_of_eq ?_) ht
    apply Finset.sum_congr rfl
    intro ω _
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> rfl
  have hk (x : G) (hx : x∈K) : (1/4:ℝ)≤f x := by
    have h := p.prob_and_split Good (fun ω => x∈E ω)
    have hu : u x<1/4 := (Finset.mem_filter.mp hx).2
    change f x+u x=p.prob Good at h
    linarith only [hu,h,hG]
  have hl : (K.card:ℝ)/4 ≤ ∑ x∈K, f x := by
    have h := Finset.sum_le_sum (s := K) (fun x hx => hk x hx)
    simpa only [Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv,one_mul] using h
  have hr : (∑ x∈K, f x) ≤ ∑ x:G, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ K)
      (fun x _ _ => p.prob_nonneg _)
  change (K.card:ℝ)≤4*e
  linarith only [hl,hr,hsum]

omit [Fintype G] in
lemma mixed_floor (p : FinLaw Ω) (q : Ω → FinLaw Γ) (Good : Ω → Prop)
    (E : Ω → Finset G) (hit : Γ → G → Prop) {τ : ℝ} (hτ : 0≤τ)
    (hq : ∀ ω, Good ω → ∀ x∉E ω, τ≤(q ω).prob (fun v => hit v x))
    (x : G) (hx : (1/4:ℝ)≤p.prob (fun ω => Good ω ∧ x∉E ω)) :
    τ/4 ≤ (p.mix q).prob (fun v => hit v x) := by
  rw [prob_mix]
  have h (ω : Ω) : τ*(if Good ω ∧ x∉E ω then (1:ℝ) else 0) ≤ (q ω).prob (fun v => hit v x) := by
    by_cases hg : Good ω ∧ x∉E ω
    · rw [ite_eq_left hg,mul_one]
      exact hq ω hg.1 x hg.2
    · rw [ite_eq_right hg,mul_zero]
      exact (q ω).prob_nonneg _
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
    mul_le_mul_of_nonneg_left (h ω) (p.nonneg ω))
  have he : (∑ ω, p ω*(τ*(if Good ω ∧ x∉E ω then (1:ℝ) else 0))) =
      τ*p.prob (fun ω => Good ω ∧ x∉E ω) := by
    rw [prob,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> ring
  rw [he] at hh
  have hm := mul_le_mul_of_nonneg_left hx hτ
  linarith only [hh,hm]

lemma prob_exists_eq_sum_disjoint {ι : Type uIota} [Fintype ι]
    (p : FinLaw Ω) (E : ι → Ω → Prop)
    (h : ∀ ω i j, E i ω → E j ω → i=j) :
    p.prob (fun ω => ∃ i, E i ω) = ∑ i, p.prob (E i) := by
  simp only [prob]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases he : ∃ i, E i ω
  · obtain ⟨i,hi⟩ := he
    rw [ite_eq_left ⟨i,hi⟩,Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      exact ite_eq_right (fun hj => hji (h ω j i hj hi))
    · simp
  · simp only [ite_eq_right he]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (fun hi => he ⟨i,hi⟩)

end FinLaw

section
namespace FinLaw
open scoped BigOperators Classical
variable {Ω : Type uOmega} {ι : Type uIota} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} [Fintype Ω] [Fintype ι] [Fintype α] [Fintype β]

lemma Hf_id (p : FinLaw Ω) : p.Hf id = p.entropy := by rw [Hf_eq_H,H,map_id]

lemma cHf_joint_fst (p : FinLaw ι) (q : ι → FinLaw Ω) (X : ι → Ω → γ) :
    (p.joint q).cHf (fun v => X v.1 v.2) Prod.fst = ∑ i, p i*(q i).Hf (X i) := by
  unfold cHf
  rw [Hf_pair_comm,Hf_joint_pair_vary]
  have h := (p.joint q).Hf_map Prod.fst id
  rw [joint_map_fst,Hf_id] at h
  change p.entropy = (p.joint q).Hf Prod.fst at h
  rw [← h]
  ring

lemma joint_iid_eval (p : FinLaw ι) (q : ι → FinLaw Ω) (n : ℕ) (i : Fin n) :
    (p.joint (fun a => (q a).iid n)).map (fun v => (v.1,v.2 i)) = p.joint q := by
  calc
    _ = p.joint (fun a => ((q a).iid n).map (fun x : Fin n → Ω => x i)) :=
      joint_map_second p (fun a => (q a).iid n) (fun x : Fin n → Ω => x i)
    _ = _ := by simp only [iid_map_eval]

theorem conditional_iid_information (p : FinLaw (α × β)) (q : α × β → FinLaw Ω) (n : ℕ) :
    (p.joint (fun a => (q a).iid n)).cIf (fun v => v.1.2) Prod.snd (fun v => v.1.1) ≤
      (n:ℝ)*(p.joint q).cIf (fun v => v.1.2) Prod.snd (fun v => v.1.1) := by
  let P := p.joint (fun a => (q a).iid n)
  let Q := p.joint q
  have hsub := P.cHf_fintype_subadd Prod.snd (fun v => v.1.1)
  have hmarg (i : Fin n) : P.cHf (fun v => v.2 i) (fun v => v.1.1) =
      Q.cHf Prod.snd (fun v => v.1.1) := by
    have h := P.cHf_map (fun v => (v.1,v.2 i)) Prod.snd (fun v => v.1.1)
    rw [joint_iid_eval] at h
    exact h.symm
  simp only [hmarg,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsub
  have hcond : P.cHf Prod.snd (fun v => (v.1.1,v.1.2)) =
      (n:ℝ)*Q.cHf Prod.snd (fun v => (v.1.1,v.1.2)) := by
    change P.cHf Prod.snd Prod.fst = (n:ℝ)*Q.cHf Prod.snd Prod.fst
    rw [cHf_joint_fst p (fun a => (q a).iid n) (fun _ x => x),
      cHf_joint_fst p q (fun _ x => x)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    change p a*((q a).iid n).Hf id = (n:ℝ)*(p a*(q a).Hf id)
    rw [Hf_id,Hf_id,entropy_iid]
    ring
  change P.cIf _ _ _ ≤ (n:ℝ)*Q.cIf _ _ _
  rw [P.cIf_comm,Q.cIf_comm]
  unfold cIf
  rw [hcond]
  linarith only [hsub]

end FinLaw

open scoped BigOperators Classical
namespace FinLaw
variable {Ω : Type uOmega} {α : Type uAlpha} {Γ : Type uCapitalGamma} {G : Type uGroup} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype G]

noncomputable def passingList (hit : Γ → G → Prop) (n : ℕ) (v : Fin n → Γ) : Finset G :=
  Finset.univ.filter (fun x => ∀ i, ¬ hit (v i) x)

lemma expect_card_passingList (q : FinLaw Γ) (hit : Γ → G → Prop)
    (E : Finset G) {c : ℝ} (hhit : ∀ x ∉ E, c≤q.prob (fun v => hit v x)) (n : ℕ) :
    (∑ v, q.iid n v*((passingList hit n v).card:ℝ)) ≤
      (E.card:ℝ)+(Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*c) := by
  have hprob (x : G) (hx : x ∉ E) :
      (q.iid n).prob (fun v => x∈passingList hit n v) ≤ Real.exp (-(n:ℝ)*c) := by
    have hh := q.iid_survival_exp (fun v => ¬hit v x) n (c := c) (by
      rw [q.prob_compl]; linarith only [hhit x hx])
    simpa only [passingList,Finset.mem_filter,Finset.mem_univ,true_and] using hh
  have he : (∑ v, q.iid n v*((passingList hit n v).card:ℝ)) =
      ∑ x : G, (q.iid n).prob (fun v => x∈passingList hit n v) := by
    have hc (v : Fin n → Γ) : ((passingList hit n v).card:ℝ) =
        ∑ x : G, if x∈passingList hit n v then (1:ℝ) else 0 := by simp
    simp only [hc,Finset.mul_sum,prob]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro v _
    by_cases hx : x∈passingList hit n v <;> simp only [hx,ite_true,ite_false,mul_one,mul_zero]
  rw [he]
  have hh (x : G) : (q.iid n).prob (fun v => x∈passingList hit n v) ≤
      (if x∈E then (1:ℝ) else 0)+Real.exp (-(n:ℝ)*c) := by
    by_cases hx : x∈E
    · simp only [hx,ite_true]
      exact ((q.iid n).prob_le_one _).trans (le_add_of_nonneg_right (Real.exp_nonneg _))
    · simp only [hx,ite_false,zero_add]
      exact hprob x hx
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hh x)
  simpa only [Finset.sum_add_distrib,Finset.sum_boole,Finset.filter_mem_eq_inter,
    Finset.univ_inter,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hs

lemma passingList_true (q : FinLaw Γ) (hit : Γ → G → Prop) (x : G)
    (h : ∀ v, q v≠0 → ¬hit v x) (n : ℕ) :
    ∀ v, q.iid n v≠0 → x∈passingList hit n v := by
  intro v hv
  simp only [passingList,Finset.mem_filter,Finset.mem_univ,true_and]
  intro i
  apply h
  intro hz
  apply hv
  change (∏ j : Fin n, q (v j)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ i) hz

lemma expect_log_le_log_expect (p : FinLaw Ω) (f : Ω → ℝ)
    (hf : ∀ ω, p ω≠0 → 0<f ω) :
    (∑ ω, p ω*Real.log (f ω)) ≤ Real.log (∑ ω, p ω*f ω) := by
  let f' := fun ω => if p ω=0 then (1:ℝ) else f ω
  have hh := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (fun ω _ => p.nonneg ω) p.sum_one (fun ω _ => show 0<f' ω from by
      dsimp only [f']; split_ifs with hz; norm_num; exact hf ω hz)
  have he (ω : Ω) : p ω*f' ω=p ω*f ω := by
    dsimp only [f']; split_ifs with hz; simp [hz]; rfl
  have hl (ω : Ω) : p ω*Real.log (f' ω)=p ω*Real.log (f ω) := by
    dsimp only [f']; split_ifs with hz; simp [hz]; rfl
  simpa only [smul_eq_mul,he,hl] using hh

lemma expected_log_card_passingList (q : FinLaw Γ) (hit : Γ → G → Prop)
    (x : G) (htrue : ∀ v, q v≠0 → ¬hit v x)
    (E : Finset G) {c : ℝ} (hhit : ∀ y ∉ E, c≤q.prob (fun v => hit v y)) (n : ℕ) :
    (∑ v, q.iid n v*Real.log (passingList hit n v).card) ≤
      Real.log ((E.card:ℝ)+(Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*c)) := by
  have hp (v : Fin n → Γ) (hv : q.iid n v≠0) : (0:ℝ)<(passingList hit n v).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨x,q.passingList_true hit x htrue n v hv⟩
  apply ((q.iid n).expect_log_le_log_expect (fun v => ((passingList hit n v).card:ℝ)) hp).trans
  apply Real.log_le_log ?_ (q.expect_card_passingList hit E hhit n)
  have hex : ∃ v, 0 < q.iid n v := by
    by_contra hh
    push Not at hh
    have hz : ∀ v, q.iid n v=0 := fun v => le_antisymm (hh v) ((q.iid n).nonneg v)
    have hs := (q.iid n).sum_one
    simp only [hz,Finset.sum_const_zero] at hs
    norm_num at hs
  obtain ⟨v,hv⟩ := hex
  exact Finset.sum_pos' (fun v _ => mul_nonneg ((q.iid n).nonneg v) (Nat.cast_nonneg _))
    ⟨v,Finset.mem_univ v,mul_pos hv (hp v hv.ne')⟩

lemma conditional_passing_support (p : FinLaw Ω) (X : Ω → G) (C : Ω → α)
    (hit : α → G → Prop) (hs : ∀ ω, p ω≠0 → ¬hit (C ω) (X ω)) :
    p.cHf X C ≤ ∑ a, p.map C a*Real.log ((Finset.univ.filter (fun x => ¬hit a x)).card) := by
  have h := p.condH_le_support X C (fun a => Finset.univ.filter (fun x => ¬hit a x)) (by
    intro ω hw
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact hs ω hw)
  simpa only [condH,← Hf_eq_H,cHf] using h

end FinLaw
end

namespace FinLaw
open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} [Fintype Ω]

lemma cHf_prefix_step (p : FinLaw Ω) {n k : ℕ} (X : Ω → Fin n → α)
    (C : Ω → β) (hk : k<n) :
    p.cHf (prefixVar X (Equiv.refl _) (k+1)) C =
      p.cHf (prefixVar X (Equiv.refl _) k) C+
        p.cHf (fun ω => X ω ⟨k,hk⟩) (fun ω => (prefixVar X (Equiv.refl _) k ω,C ω)) := by
  have he : p.cHf (prefixVar X (Equiv.refl _) (k+1)) C =
      p.cHf (fun ω => (prefixVar X (Equiv.refl _) k ω,X ω ⟨k,hk⟩)) C := by
    apply p.cHf_eq_of_fibers
    intro ω ν _
    constructor
    · intro h
      refine Prod.ext ?_ ?_
      · funext i
        by_cases hi : i.val<k
        · simpa only [prefixVar,hi,ite_eq_left,show i.val<k+1 by omega] using congrFun h i
        · simp [prefixVar,hi]
      · simpa [prefixVar] using congrFun h ⟨k,hk⟩
    · intro h
      funext i
      by_cases hi : i.val<k
      · simpa only [prefixVar,hi,ite_eq_left,show i.val<k+1 by omega] using
          congrFun (congrArg Prod.fst h) i
      · by_cases hie : i.val=k
        · have hi' : i=⟨k,hk⟩ := Fin.ext hie
          subst i
          simpa [prefixVar] using congrArg some (congrArg Prod.snd h)
        · simp [prefixVar,show ¬i.val<k+1 by omega]
  rw [he,p.cHf_chain]

lemma cHf_blocks_le (p : FinLaw Ω) {n : ℕ} (X : Ω → Fin n → α)
    (C : Ω → β) (S : Fin n → Ω → γ)
    (hS : ∀ i ω ν, prefixVar X (Equiv.refl _) i.val ω=prefixVar X (Equiv.refl _) i.val ν →
      C ω=C ν → S i ω=S i ν) :
    p.cHf X C ≤ ∑ i : Fin n, p.cHf (fun ω => X ω i) (S i) := by
  have h (k : ℕ) (hk : k≤n) : p.cHf (prefixVar X (Equiv.refl _) k) C ≤
      ∑ i : Fin k, p.cHf (fun ω => X ω ⟨i.val,by omega⟩) (S ⟨i.val,by omega⟩) := by
    induction k with
    | zero =>
      have he : p.cHf (prefixVar X (Equiv.refl _) 0) C = 0 := by
        unfold cHf
        have hh : p.Hf (fun ω => (prefixVar X (Equiv.refl _) 0 ω,C ω)) = p.Hf C := by
          apply p.Hf_eq_of_fibers
          intro ω ν
          simp only [prefixVar_zero,Prod.mk.injEq,true_and]
        rw [hh,sub_self]
      simp only [he,Finset.univ_eq_empty,Finset.sum_empty,le_refl]
    | succ k ih =>
      rw [p.cHf_prefix_step X C (by omega),Fin.sum_univ_castSucc]
      have hm := p.cHf_mono_of_refines (fun ω => X ω ⟨k,by omega⟩)
        (fun ω => (prefixVar X (Equiv.refl _) k ω,C ω)) (S ⟨k,by omega⟩)
        (fun ω ν hh => hS ⟨k,by omega⟩ ω ν (congrArg Prod.fst hh) (congrArg Prod.snd hh))
      exact add_le_add (ih (by omega)) hm
  have he : p.cHf (prefixVar X (Equiv.refl _) n) C=p.cHf X C := by
    apply p.cHf_eq_of_fibers
    intro ω ν _
    constructor
    · intro h
      funext i
      simpa [prefixVar,i.isLt] using congrFun h i
    · intro h
      funext i
      simp only [prefixVar,i.isLt,ite_eq_left,Equiv.refl_apply]
      exact congrArg some (congrFun h i)
  simpa only [he] using h n le_rfl

end FinLaw
end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat
open scoped BigOperators Classical

noncomputable def incrementWord (z : ℕ → GaussianInt) (L t : ℕ) : Fin L → GaussianInt :=
  fun i => z (t+i.val+1)-z (t+i.val)

lemma incrementWord_sum (z : ℕ → GaussianInt) (L t : ℕ) :
    ∑ i, incrementWord z L t i=z (t+L)-z t := by
  simp only [incrementWord]
  rw [Fin.sum_univ_eq_sum_range (fun i => z (t+i+1)-z (t+i))]
  simpa only [Nat.add_assoc,Nat.add_zero] using
    Finset.sum_range_sub (fun i => z (t+i)) L

lemma block_displacement (z : ℕ → GaussianInt) (L k t u : ℕ)
    (h : ∀ j<k, incrementWord z L (t+j*L)=incrementWord z L (u+j*L)) :
    z (t+k*L)-z t=z (u+k*L)-z u := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := ih (fun j hj => h j (by omega))
    have hk := congrArg (fun w : Fin L → GaussianInt => ∑ i, w i) (h k (by omega))
    rw [incrementWord_sum,incrementWord_sum] at hk
    have ht : t+k*L+L=t+(k+1)*L := by ring
    have hu : u+k*L+L=u+(k+1)*L := by ring
    rw [ht,hu] at hk
    linear_combination hh+hk

lemma residue_block_update {ι : Type uIota} (f : ι → GaussianInt) (z : ℕ → GaussianInt)
    (L k t u : ℕ)
    (hQ : (fun i => residueCode (f i) (z t))=(fun i => residueCode (f i) (z u)))
    (hW : ∀ j<k, incrementWord z L (t+j*L)=incrementWord z L (u+j*L)) :
    (fun i => residueCode (f i) (z (t+k*L)))=
      (fun i => residueCode (f i) (z (u+k*L))) := by
  have hd := block_displacement z L k t u hW
  funext i
  have hh := residueCode_add (congrFun hQ i) (congrArg (residueCode (f i)) hd)
  simpa only [add_sub_cancel] using hh

theorem incrementWord_blocks_entropy {Ω : Type uOmega} {ι : Type uIota} [Fintype Ω]
    (p : FinLaw Ω) (t : Ω → ℕ) (z : ℕ → GaussianInt) (f : ι → GaussianInt)
    (L n : ℕ) (hL : 0<L) :
    p.cHf (fun ω => incrementWord z (n*L) (t ω))
      (fun ω i => residueCode (f i) (z (t ω))) ≤
      ∑ j : Fin n, p.cHf (fun ω => incrementWord z L (t ω+j.val*L))
        (fun ω i => residueCode (f i) (z (t ω+j.val*L))) := by
  let W := fun ω (j : Fin n) => incrementWord z L (t ω+j.val*L)
  let Q := fun ω i => residueCode (f i) (z (t ω))
  have hvec : p.cHf (fun ω => incrementWord z (n*L) (t ω)) Q ≤ p.cHf W Q := by
    apply p.cHf_le_of_determined
    intro ω ν h _
    funext i
    let j : Fin n := ⟨i.val/L,(Nat.div_lt_iff_lt_mul hL).mpr i.isLt⟩
    let a : Fin L := ⟨i.val%L,Nat.mod_lt _ hL⟩
    have hh := congrFun (congrFun h j) a
    have he : j.val*L+a.val=i.val := by
      dsimp only [j,a]
      simpa only [Nat.mul_comm] using Nat.div_add_mod i.val L
    simpa only [W,incrementWord,Nat.add_assoc,he] using hh
  apply hvec.trans
  apply p.cHf_blocks_le W Q
  intro j ω ν hW hQ
  apply residue_block_update f z L j.val (t ω) (t ν) hQ
  intro k hk
  have hh := congrFun hW ⟨k,lt_trans hk j.isLt⟩
  simpa only [FinLaw.prefixVar,Equiv.refl_apply,hk,ite_eq_left,Option.some.injEq,W] using hh

noncomputable def boundedWord (z : ℕ → GaussianInt) {D : ℝ}
    (hz : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (L t : ℕ) : Fin L → latticeBall D :=
  fun i => ⟨incrementWord z L t i,by
    rw [mem_latticeBall]
    simpa only [incrementWord,map_sub,← dist_eq_norm,dist_comm] using hz (t+i.val)⟩

lemma boundedWord_fibers (z : ℕ → GaussianInt) {D : ℝ}
    (hz : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (L t u : ℕ) :
    boundedWord z hz L t=boundedWord z hz L u ↔ incrementWord z L t=incrementWord z L u := by
  constructor
  · intro h
    funext i
    exact congrArg Subtype.val (congrFun h i)
  · intro h
    funext i
    exact Subtype.ext (congrFun h i)

lemma boundedWord_entropy_le {Ω : Type uOmega} [Fintype Ω] (p : FinLaw Ω) (t : Ω → ℕ)
    (z : ℕ → GaussianInt) {D : ℝ} (hz : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (L : ℕ) :
    p.Hf (fun ω => incrementWord z L (t ω)) ≤ (L:ℝ)*Real.log (latticeBall D).card := by
  have he : p.Hf (fun ω => incrementWord z L (t ω))=p.Hf (fun ω => boundedWord z hz L (t ω)) := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    exact (boundedWord_fibers z hz L (t ω) (t ν)).symm
  rw [he]
  have h := p.Hf_le_log_card_type (fun ω => boundedWord z hz L (t ω))
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow,Real.log_pow] using h

@[simp] lemma gaussianResidue_add (π z w : GaussianInt) :
    gaussianResidue π (z+w)=gaussianResidue π z+gaussianResidue π w := rfl
@[simp] lemma gaussianResidue_sub (π z w : GaussianInt) :
    gaussianResidue π (z-w)=gaussianResidue π z-gaussianResidue π w := rfl
@[simp] lemma gaussianResidue_zero (π : GaussianInt) : gaussianResidue π 0=0 := rfl

lemma short_residue_hits_disjoint (π : GaussianInt) (z : ℕ → GaussianInt)
    (hz : Function.Injective z) {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) {L : ℕ}
    (hshort : (D*L)^2 < (π.norm:ℝ)) (a t : ℕ)
    (x : GaussianInt ⧸ multiples π) (i j : Fin L)
    (hi : gaussianResidue π (z (t+i.val)-z a)=x)
    (hj : gaussianResidue π (z (t+j.val)-z a)=x) : i=j := by
  by_contra hij
  have hneq : z (t+i.val)≠z (t+j.val) := by
    intro he
    have ht := hz he
    apply hij
    apply Fin.ext
    omega
  have hh := walk_pair_displacement z hD hs t L i.val j.val (by omega) (by omega)
  rw [GaussianInt.toComplex_sub,← dist_eq_norm] at hh
  have hd : dist (z (t+i.val):ℂ) (z (t+j.val):ℂ)^2 < (π.norm:ℝ) := by
    exact (sq_le_sq₀ dist_nonneg (mul_nonneg hD (Nat.cast_nonneg L))).mpr hh |>.trans_lt hshort
  have hres : gaussianResidue π (z (t+i.val))=gaussianResidue π (z (t+j.val)) := by
    simpa only [gaussianResidue_sub,sub_left_inj] using hi.trans hj.symm
  exact not_dvd_sub_of_dist_sq_lt hneq hd ((gaussianResidue_eq _ _ _).mp hres)

lemma short_residue_hit_prob {Ω : Type uOmega} [Fintype Ω] (p : FinLaw Ω)
    (π : GaussianInt) (z : ℕ → GaussianInt) (hz : Function.Injective z)
    {D : ℝ} (hD : 0 ≤ D) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    {L : ℕ} (hshort : (D*L)^2 < (π.norm:ℝ)) (a : ℕ) (t : Ω → ℕ)
    (x : GaussianInt ⧸ multiples π) :
    p.prob (fun ω => ∃ i : Fin L, gaussianResidue π (z (t ω+i.val)-z a)=x) =
      ∑ i : Fin L, p.prob (fun ω => gaussianResidue π (z (t ω+i.val)-z a)=x) := by
  apply p.prob_exists_eq_sum_disjoint
  intro ω i j hi hj
  exact short_residue_hits_disjoint π z hz hD hs hshort a (t ω) x i j hi hj

theorem smoothed_package_hit_lower {Ω : Type uOmega} [Fintype Ω] (p : FinLaw Ω)
    (π : GaussianInt) (z : ℕ → GaussianInt) (hz : Function.Injective z)
    {D c : ℝ} (hD : 0 ≤ D) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    {L N : ℕ} (hshort : (D*L)^2 < (π.norm:ℝ)) (hLN : L ≤ N)
    (herr : (L:ℝ)/(N+1) ≤ c/2) (a : ℕ) (t : Ω → ℕ)
    (x : GaussianInt ⧸ multiples π)
    (hfloor : c ≤ (p.joint (fun _ => FinLaw.uniform (Fin (N+1)))).prob
      (fun v => gaussianResidue π (z (t v.1+v.2.val)-z a)=x)) :
    (L:ℝ)*c/2 ≤ (p.joint (fun _ => FinLaw.uniform (Fin (N+1)))).prob
      (fun v => ∃ i : Fin L, gaussianResidue π (z (t v.1+v.2.val+i.val)-z a)=x) := by
  rw [short_residue_hit_prob _ π z hz hD hs hshort a]
  have hh (i : Fin L) : c/2 ≤
      (p.joint (fun _ => FinLaw.uniform (Fin (N+1)))).prob
        (fun v => gaussianResidue π (z (t v.1+v.2.val+i.val)-z a)=x) := by
    have hp := p.smoothing_prob t N i.val (by omega)
      (fun b => gaussianResidue π (z b-z a)=x)
    have he : (i.val:ℝ)/(N+1) ≤ c/2 := by
      apply le_trans _ herr
      exact div_le_div_of_nonneg_right (by exact_mod_cast i.isLt.le) (by positivity)
    linarith only [hp,hfloor,he]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_div_assoc] using h

lemma true_residue_no_hit (π : GaussianInt) (z : ℕ → GaussianInt)
    (havoid : ∀ t, ¬π ∣ z t) (a t L : ℕ) :
    ¬∃ i : Fin L, gaussianResidue π (z (t+i.val)-z a) = -gaussianResidue π (z a) := by
  rintro ⟨i,hi⟩
  have hh : gaussianResidue π (z (t+i.val))=gaussianResidue π 0 := by
    rw [gaussianResidue_sub] at hi
    rw [gaussianResidue_zero]
    exact sub_eq_neg_self.mp hi
  have hd := (gaussianResidue_eq _ _ _).mp hh
  simp only [sub_zero] at hd
  exact havoid _ hd

namespace FinLaw
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} {δ : Type uDelta} [Fintype Ω]

lemma cHf_congr_fibers (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (C : Ω → γ) (D : Ω → δ)
    (hX : ∀ ω ν, X ω=X ν ↔ Y ω=Y ν) (hC : ∀ ω ν, C ω=C ν ↔ D ω=D ν) :
    p.cHf X C=p.cHf Y D := by
  unfold cHf
  rw [p.Hf_eq_of_fibers C D hC]
  congr 1
  apply p.Hf_eq_of_fibers
  intro ω ν
  simp only [Prod.mk.injEq,hX,hC]

end FinLaw

lemma residueCode_vector_fibers {ι : Type uIota} (f : ι → GaussianInt) (x y : GaussianInt) :
    (fun i => residueCode (f i) x)=(fun i => residueCode (f i) y) ↔
      (fun i => gaussianResidue (f i) x)=(fun i => gaussianResidue (f i) y) := by
  simp only [funext_iff,residueCode_eq,gaussianResidue_eq]

theorem word_residue_smoothing {Ω : Type uOmega} {ι : Type uIota} [Fintype Ω] [Fintype ι]
    (p : FinLaw Ω) (t : Ω → ℕ) (z : ℕ → GaussianInt) {D : ℝ}
    (hz : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (f : ι → GaussianInt) (hf : ∀ i, f i≠0) (L N a : ℕ) (ha : a≤N) :
    let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
    P.cHf (fun v => incrementWord z L (t v.1+v.2.val+a))
      (fun v i => residueCode (f i) (z (t v.1+v.2.val+a))) ≤
    P.cHf (fun v => incrementWord z L (t v.1+v.2.val))
      (fun v i => residueCode (f i) (z (t v.1+v.2.val)))+
      2*Real.binEntropy ((a:ℝ)/(N+1))+
      ((a:ℝ)/(N+1))*((L:ℝ)*Real.log (latticeBall D).card+
        2*∑ i, Real.log (f i).norm.natAbs) := by
  let (i : ι) : Finite (GaussianInt ⧸ multiples (f i)) := finite_gaussianResidue (hf i)
  let (i : ι) : Fintype (GaussianInt ⧸ multiples (f i)) := Fintype.ofFinite _
  dsimp only
  let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
  have he (u : Ω × Fin (N+1) → ℕ) :
      P.cHf (fun v => incrementWord z L (u v)) (fun v i => residueCode (f i) (z (u v))) =
      P.condH (fun v => boundedWord z hz L (u v)) (fun v i => gaussianResidue (f i) (z (u v))) := by
    rw [show P.condH (fun v => boundedWord z hz L (u v))
      (fun v i => gaussianResidue (f i) (z (u v))) =
      P.cHf (fun v => boundedWord z hz L (u v))
      (fun v i => gaussianResidue (f i) (z (u v))) by
        simp only [FinLaw.condH,FinLaw.cHf,FinLaw.Hf_eq_H]]
    apply P.cHf_congr_fibers
    · intro v w; exact (boundedWord_fibers z hz L (u v) (u w)).symm
    · intro v w; exact residueCode_vector_fibers f _ _
  have h := p.smoothing_condH t N a ha (boundedWord z hz L)
    (fun t i => gaussianResidue (f i) (z t))
  have hc : Real.log (Fintype.card ((i : ι) → GaussianInt ⧸ multiples (f i))) =
      ∑ i, Real.log (f i).norm.natAbs := by
    rw [Fintype.card_pi,Nat.cast_prod,Real.log_prod]
    · apply Finset.sum_congr rfl
      intro i _
      rw [← Nat.card_eq_fintype_card,multiples_index (hf i)]
    · intro i _
      exact_mod_cast Fintype.card_ne_zero
  change P.cHf _ _ ≤ P.cHf _ _+_+_
  rw [he,he]
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow,
    Real.log_pow,hc] using h

end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat
open scoped BigOperators Classical

abbrev SplitSieve.SignedIndex (s : SplitSieve) := (Fin s.primes.card → Bool) × Fin s.primes.card

noncomputable def SplitSieve.signedPrime (s : SplitSieve) (i : s.SignedIndex) : ℕ :=
  s.enumeration i.2
noncomputable def SplitSieve.signedFactorAt (s : SplitSieve) (i : s.SignedIndex) : GaussianInt :=
  signedFactor (s.factor (s.signedPrime i)) (i.1 i.2)

lemma SplitSieve.signedFactorAt_norm (s : SplitSieve) (i : s.SignedIndex) :
    (s.signedFactorAt i).norm = (s.signedPrime i:ℤ) := by
  rw [signedFactorAt,signedFactor_norm]
  exact s.factor_norm _ (s.enumeration i.2).property

lemma SplitSieve.signedFactorAt_ne_zero (s : SplitSieve) (i : s.SignedIndex) :
    s.signedFactorAt i≠0 := by
  intro h
  have hn := s.signedFactorAt_norm i
  rw [h] at hn
  have hp := (s.prime_mem _ (s.enumeration i.2).property).ne_zero
  apply hp
  change s.signedPrime i = 0
  simpa only [Zsqrtd.norm_zero,Nat.cast_eq_zero] using hn.symm

abbrev SplitSieve.Residue (s : SplitSieve) (i : s.SignedIndex) :=
  GaussianInt ⧸ multiples (s.signedFactorAt i)
noncomputable instance SplitSieve.residueFintype (s : SplitSieve) (i : s.SignedIndex) :
    Fintype (s.Residue i) := by
  let := finite_gaussianResidue (s.signedFactorAt_ne_zero i)
  exact Fintype.ofFinite _

lemma SplitSieve.residue_card (s : SplitSieve) (i : s.SignedIndex) :
    Fintype.card (s.Residue i)=s.signedPrime i := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (GaussianInt ⧸ multiples (s.signedFactorAt i)) = _
  rw [multiples_index (s.signedFactorAt_ne_zero i),s.signedFactorAt_norm]
  simp

noncomputable def SplitSieve.residue (s : SplitSieve) (i : s.SignedIndex) :
    GaussianInt → s.Residue i := gaussianResidue (s.signedFactorAt i)

lemma SplitSieve.residue_fibers (s : SplitSieve) (i : s.SignedIndex) (z w : GaussianInt) :
    s.residue i z=s.residue i w ↔ s.residueVector i.1 z i.2=s.residueVector i.1 w i.2 := by
  change gaussianResidue _ z=gaussianResidue _ w ↔ residueCode _ z=residueCode _ w
  rw [gaussianResidue_eq,residueCode_eq]
  rfl

lemma FinLaw.uniform_expect {ι : Type uIota} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    (∑ i, FinLaw.uniform ι i*f i)=𝔼 i, f i := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [FinLaw.uniform_mass,← Finset.mul_sum,div_eq_inv_mul]

lemma SplitSieve.signedIndex_nonempty (s : SplitSieve) (hne : s.primes.Nonempty) :
    Nonempty s.SignedIndex := by
  have hk := hne.card_pos
  exact ⟨(fun _ => true,⟨0,hk⟩)⟩

theorem SplitSieve.signed_coverage_deficit {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω]
    (s : SplitSieve) (hne : s.primes.Nonempty) (p : FinLaw Ω)
    (Z : Ω → GaussianInt) (C : Ω → α) (a : GaussianInt) {b : ℕ}
    (hb : 0<b) (hbk : b ≤ s.primes.card) {e E : ℝ}
    (hH : (1-e)*(b:ℝ)*s.meanLog ≤ s.pointEntropy p Z b)
    (hC : p.Hf C≤E) :
    letI := s.signedIndex_nonempty hne
    (∑ i : s.SignedIndex, FinLaw.uniform _ i*(Real.log (Fintype.card (s.Residue i))-
      p.cHf (fun ω => s.residue i (Z ω-a)) C)) ≤ e*s.meanLog+E/b := by
  let := s.signedIndex_nonempty hne
  have hc := s.coverage_conditioning p Z C hbk
  have he (i : s.SignedIndex) :
      p.cHf (fun ω => s.residue i (Z ω-a)) C =
        p.cHf (fun ω => s.residueVector i.1 (Z ω) i.2) C := by
    apply p.cHf_congr_fibers _ _ _ _
    · intro ω ν
      change gaussianResidue _ (Z ω-a)=gaussianResidue _ (Z ν-a) ↔ _
      rw [gaussianResidue_sub,gaussianResidue_sub,sub_left_inj]
      exact s.residue_fibers i _ _
    · intro ω ν; rfl
  have hd : (∑ i : s.SignedIndex, FinLaw.uniform _ i*
      (Real.log (Fintype.card (s.Residue i))-p.cHf (fun ω => s.residue i (Z ω-a)) C)) =
      s.meanLog-(𝔼 σ : Fin s.primes.card → Bool, 𝔼 i : Fin s.primes.card,
        p.cHf (fun ω => s.residueVector σ (Z ω) i) C) := by
    rw [FinLaw.uniform_expect]
    simp only [s.residue_card,he,Finset.expect_sub_distrib]
    simp only [← Finset.univ_product_univ,Finset.expect_product]
    simp only [signedPrime,meanLog,Fintype.expect_const]
  rw [hd]
  have hbp : (0:ℝ)<b := by exact_mod_cast hb
  apply (mul_le_mul_iff_left₀ hbp).mp
  have hgoal : (s.meanLog-(𝔼 σ : Fin s.primes.card → Bool, 𝔼 i : Fin s.primes.card,
      p.cHf (fun ω => s.residueVector σ (Z ω) i) C))*(b:ℝ) ≤
        (e*s.meanLog+E/b)*(b:ℝ) := by
    rw [add_mul,div_mul_cancel₀ _ hbp.ne']
    linarith only [hc,hH,hC]
  exact hgoal

namespace FinLaw
variable {G : Type uGroup} [Fintype G]

noncomputable def lowResidues (p : FinLaw G) (τ : ℝ) : Finset G :=
  Finset.univ.filter (fun x => p x<τ/(Fintype.card G:ℝ))

lemma not_mem_lowResidues (p : FinLaw G) (τ : ℝ) (x : G) :
    x∉p.lowResidues τ ↔ τ/(Fintype.card G:ℝ)≤p x := by
  simp only [lowResidues,Finset.mem_filter,Finset.mem_univ,true_and,not_lt]

lemma lowResidues_prob (p : FinLaw G) (τ : ℝ) :
    p.prob (fun x => x∈p.lowResidues τ) ≤ τ*(p.lowResidues τ).card/(Fintype.card G:ℝ) := by
  have he : p.prob (fun x => x∈p.lowResidues τ)=∑ x∈p.lowResidues τ, p x := by
    unfold prob
    trans ∑ x, if x∈p.lowResidues τ then p.mass x else 0
    · apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> rfl
    · rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
  rw [he]
  have hh := Finset.sum_le_sum (s := p.lowResidues τ) (fun x hx =>
    ((Finset.mem_filter.mp hx).2).le)
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  have heq : ((p.lowResidues τ).card:ℝ)*(τ/(Fintype.card G:ℝ)) =
      τ*(p.lowResidues τ).card/(Fintype.card G:ℝ) := by ring
  rw [heq] at hh
  exact hh

lemma lowResidues_equiv {G' : Type uGroupPrime} [Fintype G'] (p : FinLaw G) (e : G ≃ G') (τ : ℝ) :
    ((p.map e).lowResidues τ).card=(p.lowResidues τ).card := by
  have h : (p.map e).lowResidues τ=(p.lowResidues τ).image e := by
    ext x
    simp only [lowResidues,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_image,map_equiv_mass,Fintype.card_congr e]
    constructor
    · intro hx
      exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
    · rintro ⟨y,hy,rfl⟩
      simpa only [e.symm_apply_apply] using hy
  rw [h,Finset.card_image_of_injective _ e.injective]

theorem lowResidues_base {ι : Type uIota} [Fintype ι]
    (G : ι → Type uGroup) [∀ i, Fintype (G i)] (w : FinLaw ι)
    (p : (i : ι) → FinLaw (G i)) (u : ι → ℝ) {τ b e : ℝ}
    (hτ : τ≤3/8) (hb : 0<b)
    (hu : ∀ i, 8*b*(Fintype.card (G i):ℝ) ≤ u i)
    (hdef : (∑ i, w i*(Real.log (Fintype.card (G i))-(p i).entropy))≤e) :
    w.prob (fun i => u i≤((p i).lowResidues τ).card) ≤ e/b := by
  apply low_mass_average G w p (fun i => (p i).lowResidues τ) _ hb
  · intro i x hx
    exact ((Finset.mem_filter.mp hx).2).le.trans
      (div_le_div_of_nonneg_right hτ (Nat.cast_nonneg _))
  · intro i hi
    have hne := (p i).nonempty
    have hp : (0:ℝ)<Fintype.card (G i) := by exact_mod_cast Fintype.card_pos
    apply (le_div_iff₀ (by positivity : (0:ℝ)<8*(Fintype.card (G i):ℝ))).mpr
    linarith only [hu i,hi]
  · exact hdef

theorem lowResidues_backward {Ω : Type uOmega} {Γ : Type uCapitalGamma} {ι : Type uIota} [Fintype Ω] [Fintype Γ] [Fintype ι]
    (G : ι → Type uGroup) [∀ i, Fintype (G i)] [∀ i, AddCommGroup (G i)]
    (w : FinLaw ι) (p : FinLaw Ω) (q : Ω → FinLaw Γ)
    (Y : (i : ι) → Ω → G i) (h : (i : ι) → Γ → G i)
    (u u' b : ι → ℝ) {τ δ ε η η' e v : ℝ} {n : ℕ}
    (hn : 0<n) (hτ : 0≤τ) (hτ1 : τ≤3/8) (hδ : 0<δ) (hδ1 : δ≤1/64)
    (hε : 0≤ε) (hη : 0<η) (hu : ∀ i, 0<u i)
    (hnext : ∑ i, w i*p.prob (fun ω => u' i≤
      (((q ω).map (h i)).lowResidues (τ+4*δ)).card) ≤ η')
    (hsmall : η'+ε≤η*δ/2) (hscale : 2*(1-Real.log (η*δ/2))≤v)
    (hgap : e<η*δ*v/4)
    (hdata : (∑ i, w i*(Real.log (Fintype.card (G i))-
      (p.joint (fun ω => (q ω).iid n)).cHf (fun x => Y i x.1) Prod.snd))≤e)
    (hb : ∀ i, 1≤b i)
    (hv : ∀ i, v≤Real.log (Fintype.card (G i))-Real.log (b i))
    (hu' : ∀ i, u' i/δ≤b i)
    (herr : ∀ i, (Fintype.card (G i):ℝ)*
      Real.exp (-(n:ℝ)*δ^2*u i/(2*(Fintype.card (G i):ℝ)))≤ε) :
    w.prob (fun i => u i≤(((p.joint q).map (fun x => Y i x.1+h i x.2)).lowResidues τ).card) ≤ η := by
  let P := fun i => (p.joint q).map (fun x => Y i x.1+h i x.2)
  let K := fun i => (P i).lowResidues τ
  let B₀ := fun i => u i≤(K i).card
  let B₁ := fun i ω => u' i≤(((q ω).map (h i)).lowResidues (τ+4*δ)).card
  let E := fun i ω => (((q ω).map (h i)).lowResidues (τ+4*δ))
  apply backward_coverage_step G w p q Y h B₀ B₁ K E b hn hτ hτ1 hδ hδ1
    hε hη hnext hsmall hscale hgap hdata
  · intro i hi
    apply Finset.card_pos.mp
    have hh : (0:ℝ)<(K i).card := (hu i).trans_le hi
    exact_mod_cast hh
  · intro i _; exact hb i
  · intro i _; exact hv i
  · intro i _
    have hh := (P i).lowResidues_prob τ
    rw [prob_map] at hh
    exact hh
  · intro i _ ω _ x hx
    exact (((q ω).map (h i)).not_mem_lowResidues _ x).mp hx
  · intro i _ ω hω
    have hh : ((E i ω).card:ℝ)<u' i := lt_of_not_ge hω
    exact (div_le_div_of_nonneg_right hh.le hδ.le).trans (hu' i)
  · intro i hi
    apply le_trans _ (herr i)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hi (show 0≤(n:ℝ)*δ^2 by positivity)
    have hd := div_le_div_of_nonneg_right hh
      (show 0≤2*(Fintype.card (G i):ℝ) by positivity)
    simpa only [neg_mul,neg_div] using neg_le_neg hd

end FinLaw
end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat
open scoped BigOperators Classical

noncomputable def ForwardKernel.displacementSymbol (K : ForwardKernel)
    (z : ℕ → GaussianInt) {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (a : ℕ) :
    Fin (K.bound+1) → latticeBall (D*K.bound) := fun i =>
  ⟨z (a+i.val)-z a,(mem_latticeBall _ _).mpr (by
    simpa only [Nat.add_zero] using walk_pair_displacement z hD hs a K.bound i.val 0
      (by omega) (by omega))⟩

noncomputable def ForwardKernel.displacementLaw (K : ForwardKernel)
    (z : ℕ → GaussianInt) {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (a : ℕ) :
    FinLaw (latticeBall (D*K.bound)) :=
  (K.law a).map (K.displacementSymbol z hD hs a)

lemma ForwardKernel.displacementLaw_observe (K : ForwardKernel)
    (z : ℕ → GaussianInt) {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (a : ℕ)
    {α : Type uAlpha} [Fintype α] (f : GaussianInt → α) :
    (K.displacementLaw z hD hs a).map (fun d => f (d.val+z a))=
      (K.law a).map (fun i => f (z (a+i.val))) := by
  rw [displacementLaw,FinLaw.map_comp]
  congr 1
  funext i
  simp only [Function.comp_def,displacementSymbol,sub_add_cancel]

theorem continuation_data_entropy {Ω : Type uOmega} [Fintype Ω] (p : FinLaw Ω)
    (a : Ω → ℕ) (K : ForwardKernel) (z : ℕ → GaussianInt) {D : ℝ}
    (hD : 1≤D) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (hK : 1≤K.bound) (n : ℕ) :
    (p.joint (fun ω => (K.displacementLaw z (by linarith only [hD]) hs (a ω)).iid n)).Hf
      Prod.snd ≤ n*(Real.log 36+2*Real.log (D*K.bound)) := by
  let q := fun ω => (K.displacementLaw z (by linarith only [hD]) hs (a ω)).iid n
  have hh := (p.joint q).Hf_le_log_card_type Prod.snd
  simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow,Real.log_pow] at hh
  have hR : 1≤D*K.bound := one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast hK)
  have hc : (0:ℝ)<(latticeBall (D*K.bound)).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0,by simpa using (show 0≤D*K.bound by positivity)⟩
  have hl := Real.log_le_log hc (latticeBall_card_le hR)
  rw [Real.log_mul (by norm_num : (36:ℝ)≠0)
    (pow_ne_zero _ (by linarith only [hR] : D*K.bound≠0)),Real.log_pow] at hl
  exact hh.trans (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _))

lemma continuation_pointEntropy {Ω : Type uOmega} [Fintype Ω] (s : SplitSieve)
    (p : FinLaw Ω) (a : Ω → ℕ) (K : ForwardKernel) (z : ℕ → GaussianInt) {D : ℝ}
    (hD : 0≤D) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (n b : ℕ) :
    s.pointEntropy (p.joint (fun ω => (K.displacementLaw z hD hs (a ω)).iid n))
      (fun v => z (a v.1)) b = s.pointEntropy p (fun ω => z (a ω)) b := by
  let q : Ω → FinLaw (Fin n → latticeBall (D*K.bound)) := fun ω =>
    (K.displacementLaw z hD hs (a ω)).iid n
  exact s.pointEntropy_joint_fst p q (fun ω => z (a ω)) b

noncomputable def ForwardKernel.relativeResidueLaw (K : ForwardKernel)
    (s : SplitSieve) (z : ℕ → GaussianInt) (a : ℕ) (i : s.SignedIndex) : FinLaw (s.Residue i) :=
  (K.law a).map (fun t => s.residue i (z (a+t.val)-z a))

lemma ForwardKernel.displacementLaw_residue (K : ForwardKernel)
    (s : SplitSieve) (z : ℕ → GaussianInt) {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (a : ℕ) (i : s.SignedIndex) :
    (K.displacementLaw z hD hs a).map (fun d => s.residue i d.val)=
      K.relativeResidueLaw s z a i := by
  rw [ForwardKernel.displacementLaw,FinLaw.map_comp]
  rfl

lemma ForwardKernel.then_relativeResidueLaw (K R : ForwardKernel)
    (s : SplitSieve) (z : ℕ → GaussianInt) {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (a : ℕ) (i : s.SignedIndex) :
    (K.then R).relativeResidueLaw s z a i =
      ((K.law a).joint (fun t => R.displacementLaw z hD hs (a+t.val))).map
        (fun v => s.residue i (z (a+v.1.val)-z a)+s.residue i v.2.val) := by
  unfold relativeResidueLaw ForwardKernel.then
  rw [FinLaw.map_comp,FinLaw.joint_observation_fun,FinLaw.joint_observation_fun]
  congr 1
  funext t
  rw [ForwardKernel.displacementLaw,FinLaw.map_comp]
  congr 1
  funext u
  change s.residue i (z (a+(t.val+u.val))-z a) =
    s.residue i (z (a+t.val)-z a)+s.residue i (z (a+t.val+u.val)-z (a+t.val))
  unfold SplitSieve.residue
  rw [← gaussianResidue_add]
  congr 1
  rw [Nat.add_assoc]
  abel

lemma FinLaw.cHf_const_right {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω]
    (p : FinLaw Ω) (X : Ω → α) (c : β) : p.cHf X (fun _ => c)=p.Hf X := by
  unfold cHf
  rw [p.Hf_const,sub_zero]
  apply p.Hf_eq_of_fibers
  intro ω ν
  simp only [Prod.mk.injEq,and_true]

lemma ForwardKernel.residue_deficit (K : ForwardKernel)
    (s : SplitSieve) (hne : s.primes.Nonempty) (z : ℕ → GaussianInt) (a : ℕ)
    {b : ℕ} (hb : 0<b) (hbk : b≤ s.primes.card) {e : ℝ}
    (hH : (1-e)*(b:ℝ)*s.meanLog≤ s.pointEntropy (K.law a) (fun t => z (a+t.val)) b) :
    letI := s.signedIndex_nonempty hne
    (∑ i : s.SignedIndex, FinLaw.uniform _ i*(Real.log (Fintype.card (s.Residue i))-
      (K.relativeResidueLaw s z a i).entropy))≤e*s.meanLog := by
  let := s.signedIndex_nonempty hne
  have hh := s.signed_coverage_deficit hne (K.law a) (fun t => z (a+t.val))
    (fun _ => ()) (z a) hb hbk hH (E := 0) (by rw [FinLaw.Hf_const])
  simp only [FinLaw.cHf_const_right,zero_div,add_zero] at hh
  change (∑ i, FinLaw.uniform _ i*(Real.log (Fintype.card (s.Residue i))-
    (K.law a).H (fun t => s.residue i (z (a+t.val)-z a))))≤_
  simpa only [FinLaw.Hf_eq_H] using hh

theorem ForwardKernel.coverage_base (K : ForwardKernel)
    (s : SplitSieve) (hne : s.primes.Nonempty) (z : ℕ → GaussianInt) (a : ℕ)
    {b : ℕ} (hb : 0<b) (hbk : b≤ s.primes.card) {e τ c : ℝ} (u : s.SignedIndex → ℝ)
    (hτ : τ≤3/8) (hc : 0<c) (hu : ∀ i, 8*c*(s.signedPrime i:ℝ)≤u i)
    (hH : (1-e)*(b:ℝ)*s.meanLog≤ s.pointEntropy (K.law a) (fun t => z (a+t.val)) b) :
    letI := s.signedIndex_nonempty hne
    (FinLaw.uniform s.SignedIndex).prob (fun i =>
      u i≤((K.relativeResidueLaw s z a i).lowResidues τ).card) ≤e*s.meanLog/c := by
  let := s.signedIndex_nonempty hne
  apply FinLaw.lowResidues_base s.Residue (FinLaw.uniform _) (K.relativeResidueLaw s z a) u
    hτ hc
  · intro i
    simpa only [s.residue_card] using hu i
  · exact K.residue_deficit s hne z a hb hbk hH

lemma ForwardKernel.coverage_data_deficit (K R : ForwardKernel)
    (s : SplitSieve) (hne : s.primes.Nonempty) (z : ℕ → GaussianInt) {D : ℝ}
    (hD : 1≤D) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (hR : 1≤R.bound)
    (a n : ℕ) {b : ℕ} (hb : 0<b) (hbk : b≤ s.primes.card) {e : ℝ}
    (hH : (1-e)*(b:ℝ)*s.meanLog≤ s.pointEntropy (K.law a) (fun t => z (a+t.val)) b) :
    letI := s.signedIndex_nonempty hne
    (∑ i : s.SignedIndex, FinLaw.uniform _ i*(Real.log (Fintype.card (s.Residue i))-
      ((K.law a).joint (fun t => (R.displacementLaw z (by linarith only [hD]) hs (a+t.val)).iid n)).cHf
        (fun v => s.residue i (z (a+v.1.val)-z a)) Prod.snd)) ≤
      e*s.meanLog+n*(Real.log 36+2*Real.log (D*R.bound))/b := by
  let := s.signedIndex_nonempty hne
  let q := fun t : Fin (K.bound+1) =>
    (R.displacementLaw z (by linarith only [hD]) hs (a+t.val)).iid n
  let P := (K.law a).joint q
  have he : s.pointEntropy P (fun v => z (a+v.1.val)) b =
      s.pointEntropy (K.law a) (fun t => z (a+t.val)) b :=
    s.pointEntropy_joint_fst (K.law a) q (fun t => z (a+t.val)) b
  have hH' : (1-e)*(b:ℝ)*s.meanLog≤ s.pointEntropy P (fun v => z (a+v.1.val)) b := by
    rw [he]; exact hH
  exact s.signed_coverage_deficit hne P (fun v => z (a+v.1.val)) Prod.snd (z a)
    hb hbk hH' (continuation_data_entropy (K.law a) (fun t => a+t.val) R z hD hs hR n)

theorem ForwardKernel.coverage_backward (K R : ForwardKernel)
    (s : SplitSieve) (hne : s.primes.Nonempty) (z : ℕ → GaussianInt) {D : ℝ}
    (hD : 1≤D) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (hR : 1≤R.bound)
    (a : ℕ) (u u' c : s.SignedIndex → ℝ) {τ δ ε η η' e v : ℝ} {n b : ℕ}
    (hn : 0<n) (hb : 0<b) (hbk : b≤ s.primes.card)
    (hτ : 0≤τ) (hτ1 : τ≤3/8) (hδ : 0<δ) (hδ1 : δ≤1/64)
    (hε : 0≤ε) (hη : 0<η) (hu : ∀ i, 0<u i)
    (hH : (1-e)*(b:ℝ)*s.meanLog≤ s.pointEntropy (K.law a) (fun t => z (a+t.val)) b)
    (hnext : ∀ t, letI := s.signedIndex_nonempty hne
      (FinLaw.uniform s.SignedIndex).prob (fun i => u' i≤
        ((R.relativeResidueLaw s z t i).lowResidues (τ+4*δ)).card)≤η')
    (hsmall : η'+ε≤η*δ/2) (hscale : 2*(1-Real.log (η*δ/2))≤v)
    (hgap : e*s.meanLog+n*(Real.log 36+2*Real.log (D*R.bound))/b<η*δ*v/4)
    (hc : ∀ i, 1≤c i) (hv : ∀ i, v≤Real.log (s.signedPrime i)-Real.log (c i))
    (hu' : ∀ i, u' i/δ≤c i)
    (herr : ∀ i, (s.signedPrime i:ℝ)*Real.exp
      (-(n:ℝ)*δ^2*u i/(2*(s.signedPrime i:ℝ)))≤ε) :
    letI := s.signedIndex_nonempty hne
    (FinLaw.uniform s.SignedIndex).prob (fun i =>
      u i≤(((K.then R).relativeResidueLaw s z a i).lowResidues τ).card)≤η := by
  let := s.signedIndex_nonempty hne
  let w := FinLaw.uniform s.SignedIndex
  let q := fun t : Fin (K.bound+1) => R.displacementLaw z (by linarith only [hD]) hs (a+t.val)
  have hnxt : (∑ i, w i*(K.law a).prob (fun t => u' i≤
      (((q t).map (fun d => s.residue i d.val)).lowResidues (τ+4*δ)).card))≤η' := by
    simp only [q,ForwardKernel.displacementLaw_residue,FinLaw.prob,Finset.mul_sum]
    rw [Finset.sum_comm]
    have he : (∑ t, ∑ i, w i*(if u' i≤
        ((R.relativeResidueLaw s z (a+t.val) i).lowResidues (τ+4*δ)).card then K.law a t else 0)) =
        ∑ t, K.law a t*w.prob (fun i => u' i≤
          ((R.relativeResidueLaw s z (a+t.val) i).lowResidues (τ+4*δ)).card) := by
      unfold FinLaw.prob
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring
    rw [he]
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun t _ =>
      mul_le_mul_of_nonneg_left (hnext (a+t.val)) ((K.law a).nonneg t))
    simpa only [← Finset.sum_mul,(K.law a).sum_one,one_mul] using hh
  have hd := K.coverage_data_deficit R s hne z hD hs hR a n hb hbk hH
  have hh := FinLaw.lowResidues_backward s.Residue w (K.law a) q
    (fun i t => s.residue i (z (a+t.val)-z a)) (fun i d => s.residue i d.val)
    u u' c hn hτ hτ1 hδ hδ1 hε hη hu hnxt hsmall hscale hgap hd hc
    (by intro i; simpa only [s.residue_card] using hv i) hu'
    (by intro i; simpa only [s.residue_card] using herr i)
  have he (i : s.SignedIndex) := K.then_relativeResidueLaw R s z
    (by linarith only [hD]) hs a i
  simpa only [he] using hh

structure EntropyBand (s : SplitSieve) (D : ℝ) (ns : List ℕ) (N b : ℕ) (δ : ℝ) where
  pre : List ℕ
  post : List ℕ
  g : ℝ
  U : ℝ
  l : ℕ
  e : ℝ
  schedule : ns=pre++List.ofFn (fun i : Fin l => bandLength g U i.val)++post
  size : b=bandSize s g U l
  positive : 0<g
  small : g≤1/200
  scale : 0<U
  logarithmic : 2*(1+Real.log 18)≤g*bandScale g U l
  large : 640*s.meanLog≤g^5*bandScale g U l
  alphabet : Real.log 16+Real.log (max D ((latticeBall (4*D)).card:ℝ))≤g^2*bandScale g U l
  displacement : 4*Real.log D+2*Real.log 36≤4*g*bandScale g U l
  geometry : 2*Real.log 16+4*Real.log D≤bandScale g U l/4
  cap : ⌊U/s.meanLog⌋₊≤ s.primes.card
  cost : Real.log 36+2*Real.log (D*((post.sum+N:ℕ)+1))≤e*(bandSize s g U l:ℝ)*s.meanLog
  deficit : (1/2:ℝ)^l+80*g+e≤δ

theorem EntropyBand.sound {s : SplitSieve} {D T : ℝ} {ns : List ℕ} {N b : ℕ} {δ : ℝ}
    (q : EntropyBand s D ns N b δ) (hne : s.primes.Nonempty)
    (z : ℕ → GaussianInt) (hz : Function.Injective z) (hD : 1≤D) (hT : 5≤T)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (hpT : ∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T) (hL : 1≤ s.meanLog) (a : ℕ) :
    (1-δ)*(b:ℝ)*s.meanLog≤
      s.pointEntropy ((commonSchedule z ns N).law a) (fun t => z (a+t.val)) b := by
  rcases q with ⟨pre,post,g,U,l,e,heq,hb,hg,hg1,hU,hlog,hlarge,hsize,hdisp,hgeom,hcap,hcost,hδ⟩
  subst ns b
  have hh := commonSchedule_subband_entropy s hne z hz pre post a N hD hT hs hpT
    hg hg1 hL hU hlog hlarge hsize hdisp hgeom hcap hcost
  have hn : 0≤(bandSize s g U l:ℝ)*s.meanLog := mul_nonneg (Nat.cast_nonneg _) (by linarith only [hL])
  nlinarith only [hh,hδ,hn]

inductive CoverageDerivation (s : SplitSieve) (D : ℝ) (N : ℕ) :
    List ℕ → ℝ → (s.SignedIndex → ℝ) → ℝ → Prop
  | base (ns : List ℕ) (b : ℕ) (τ c e η : ℝ) (u : s.SignedIndex → ℝ)
      (band : EntropyBand s D ns N b e)
      (hb : 0<b) (hbk : b≤ s.primes.card) (hτ : τ≤3/8) (hc : 0<c)
      (hu : ∀ i, 8*c*(s.signedPrime i:ℝ)≤u i) (hη : e*s.meanLog/c≤η) :
      CoverageDerivation s D N ns τ u η
  | step (ns rest : List ℕ) (b n : ℕ) (τ δ ε η η' e v : ℝ)
      (u u' c : s.SignedIndex → ℝ)
      (band : EntropyBand s D ns 0 b e)
      (next : CoverageDerivation s D N rest (τ+4*δ) u' η')
      (hR : 1≤rest.sum+N) (hn : 0<n) (hb : 0<b) (hbk : b≤ s.primes.card)
      (hτ : 0≤τ) (hτ1 : τ≤3/8) (hδ : 0<δ) (hδ1 : δ≤1/64)
      (hε : 0≤ε) (hη : 0<η) (hu : ∀ i, 0<u i)
      (hsmall : η'+ε≤η*δ/2) (hscale : 2*(1-Real.log (η*δ/2))≤v)
      (hgap : e*s.meanLog+n*(Real.log 36+2*Real.log (D*(rest.sum+N)))/b<η*δ*v/4)
      (hc : ∀ i, 1≤c i) (hv : ∀ i, v≤Real.log (s.signedPrime i)-Real.log (c i))
      (hu' : ∀ i, u' i/δ≤c i)
      (herr : ∀ i, (s.signedPrime i:ℝ)*Real.exp
        (-(n:ℝ)*δ^2*u i/(2*(s.signedPrime i:ℝ)))≤ε) :
      CoverageDerivation s D N (ns++rest) τ u η

theorem CoverageDerivation.sound {s : SplitSieve} {D T : ℝ} {N : ℕ}
    {ns : List ℕ} {τ η : ℝ} {u : s.SignedIndex → ℝ}
    (q : CoverageDerivation s D N ns τ u η) (hne : s.primes.Nonempty)
    (z : ℕ → GaussianInt) (hz : Function.Injective z) (hD : 1≤D) (hT : 5≤T)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (hpT : ∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T) (hL : 1≤ s.meanLog) :
    ∀ a, letI := s.signedIndex_nonempty hne
      (FinLaw.uniform s.SignedIndex).prob (fun i => u i≤
        (((commonSchedule z ns N).relativeResidueLaw s z a i).lowResidues τ).card)≤η := by
  let := s.signedIndex_nonempty hne
  induction q with
  | base ns b τ c e η u band hb hbk hτ hc hu hη =>
    intro a
    exact ((commonSchedule z ns N).coverage_base s hne z a hb hbk u hτ hc hu
      (band.sound hne z hz hD hT hs hpT hL a)).trans hη
  | step ns rest b n τ δ ε η η' e v u u' c band next hR hn hb hbk hτ hτ1 hδ hδ1
      hε hη hu hsmall hscale hgap hc hv hu' herr ih =>
    intro a
    rw [commonSchedule_append]
    apply (commonSchedule z ns 0).coverage_backward (commonSchedule z rest N) s hne z
      hD hs (by simpa only [commonSchedule_bound] using hR) a u u' c hn hb hbk hτ hτ1 hδ hδ1 hε hη hu
      (band.sound hne z hz hD hT hs hpT hL a) ih hsmall hscale
    · simpa only [commonSchedule_bound,Nat.cast_add] using hgap
    · exact hc
    · exact hv
    · exact hu'
    · exact herr

end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat

namespace FinLaw
open scoped BigOperators Classical

lemma cHf_dpi_subadd {Ω : Type uOmega} {ι : Type uIota} [Fintype Ω] [Fintype ι]
    (G : ι → Type uGroup) (p : FinLaw Ω) (X : (i : ι) → Ω → G i) {α : Type uAlpha} (C : Ω → α) :
    p.cHf (fun ω i => X i ω) C ≤ ∑ i, p.cHf (X i) C := by
  let Y := fun ω i => (⟨i,X i ω⟩ : Σ i, G i)
  have he : p.cHf (fun ω i => X i ω) C = p.cHf Y C := by
    apply p.cHf_congr_fibers _ _ _ _
    · intro ω ν
      constructor
      · intro h; funext i; exact congrArg (Sigma.mk i) (congrFun h i)
      · intro h; funext i; exact Sigma.mk.inj_iff.mp (congrFun h i) |>.2 |> eq_of_heq
    · intro ω ν; rfl
  rw [he]
  apply (p.cHf_fintype_subadd Y C).trans
  apply Finset.sum_le_sum
  intro i _
  apply le_of_eq
  apply p.cHf_congr_fibers _ _ _ _
  · intro ω ν
    exact ⟨fun h => eq_of_heq (Sigma.mk.inj_iff.mp h).2,fun h => congrArg (Sigma.mk i) h⟩
  · intro ω ν; rfl

lemma joint_passing_entropy {ι : Type uIota} {O : Type uOutput} {Γ : Type uCapitalGamma} [Fintype ι] [Fintype O] [Fintype Γ]
    (G : ι → Type uGroup) [∀ i, Fintype (G i)]
    (p : FinLaw (O × (∀ i, G i))) (q : O × (∀ i, G i) → FinLaw Γ)
    (hit : (i : ι) → Γ → G i → Prop) (n : ℕ)
    (htrue : ∀ a, p a≠0 → ∀ v, q a v≠0 → ∀ i, ¬ hit i v (a.2 i)) :
    (p.joint (fun a => (q a).iid n)).cHf (fun v => v.1.2)
      (fun v => (v.1.1,v.2)) ≤
      ∑ a, p a*(∑ i, ∑ v, (q a).iid n v*Real.log (passingList (hit i) n v).card) := by
  let P := p.joint (fun a => (q a).iid n)
  let C := fun v : (O × (∀ i, G i)) × (Fin n → Γ) => (v.1.1,v.2)
  have hcoordinate (i : ι) :
      P.cHf (fun v => v.1.2 i) C ≤ ∑ v, P v*Real.log (passingList (hit i) n v.2).card := by
    have hh := P.conditional_passing_support (fun v => v.1.2 i) C
      (fun c x => ∃ j, hit i (c.2 j) x) (by
        intro v hv
        have hm : p v.1≠0 ∧ (q v.1).iid n v.2≠0 := mul_ne_zero_iff.mp hv
        have hx := (q v.1).passingList_true (hit i) (v.1.2 i)
          (fun a ha => htrue v.1 hm.1 a ha i) n v.2 hm.2
        simpa only [passingList,Finset.mem_filter,Finset.mem_univ,true_and,not_exists] using hx)
    have hh' : P.cHf (fun v => v.1.2 i) C ≤
        ∑ c, (P.map C) c * Real.log (passingList (hit i) n c.2).card := by
      convert hh using 1
      apply Finset.sum_congr rfl
      intro c _
      simp only [passingList,not_exists]
    rw [expect_map] at hh'
    exact hh'
  have hs := P.cHf_dpi_subadd G (fun i v => v.1.2 i) C
  apply hs.trans
  apply (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcoordinate i)).trans
  apply le_of_eq
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum,← mul_assoc]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  simp only [P,joint_mass]

theorem passing_information_lower {ι : Type uIota} {O : Type uOutput} {Γ : Type uCapitalGamma} [Fintype ι] [Fintype O] [Fintype Γ]
    (G : ι → Type uGroup) [∀ i, Fintype (G i)]
    (p : FinLaw (O × (∀ i, G i))) (q : O × (∀ i, G i) → FinLaw Γ)
    (hit : (i : ι) → Γ → G i → Prop) (n : ℕ)
    (htrue : ∀ a, p a≠0 → ∀ v, q a v≠0 → ∀ i, ¬ hit i v (a.2 i))
    (Bad : ι → O × (∀ i, G i) → Prop) {A e η : ℝ} (hA : 0≤A)
    (hH : (∑ i, Real.log (Fintype.card (G i)))-e ≤ p.cHf Prod.snd Prod.fst)
    (hBad : (∑ i, p.prob (Bad i)) ≤ η)
    (hlist : ∀ a, p a≠0 → ∀ i,
      (∑ v, (q a).iid n v*Real.log (passingList (hit i) n v).card) ≤
        Real.log (Fintype.card (G i))-A*(if Bad i a then 0 else 1)) :
    A*((Fintype.card ι:ℝ)-η)-e ≤
      (n:ℝ)*(p.joint q).cIf (fun v => v.1.2) Prod.snd (fun v => v.1.1) := by
  let P := p.joint (fun a => (q a).iid n)
  have hcond := joint_passing_entropy G p q hit n htrue
  have hsum : (∑ a, p a*(∑ i, ∑ v, (q a).iid n v*Real.log (passingList (hit i) n v).card)) ≤
      (∑ i, Real.log (Fintype.card (G i)))-A*((Fintype.card ι:ℝ)-∑ i, p.prob (Bad i)) := by
    calc
      _ ≤ ∑ a, p a*(∑ i, (Real.log (Fintype.card (G i))-A*(if Bad i a then 0 else 1))) := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : p a=0
        · simp only [ha,zero_mul,le_refl]
        · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hlist a ha i)) (p.nonneg a)
      _ = _ := by
        simp only [Finset.sum_sub_distrib,mul_sub,
          ← Finset.sum_mul,p.sum_one,one_mul]
        congr 1
        rw [mul_comm]
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        have hh (i : ι) : (∑ a, p a*(if Bad i a then (0:ℝ) else 1))=1-p.prob (Bad i) := by
          rw [← p.prob_compl]
          unfold prob
          apply Finset.sum_congr rfl
          intro a _
          by_cases hb : Bad i a <;> simp [hb]
        have hh' (i : ι) : (∑ a, p a*(A*(if Bad i a then (0:ℝ) else 1)))=
            A*(1-p.prob (Bad i)) := by
          rw [← hh i,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
        simp only [hh',mul_sub,mul_one,Finset.sum_sub_distrib,Finset.sum_const,
          Finset.card_univ,nsmul_eq_mul]
  have hinit : P.cHf (fun v => v.1.2) (fun v => v.1.1)=p.cHf Prod.snd Prod.fst := by
    have hh := P.cHf_map Prod.fst Prod.snd Prod.fst
    rw [joint_map_fst] at hh
    exact hh.symm
  have hlow : A*((Fintype.card ι:ℝ)-η)-e ≤
      P.cIf (fun v => v.1.2) Prod.snd (fun v => v.1.1) := by
    unfold cIf
    rw [hinit]
    have hm := mul_le_mul_of_nonneg_left hBad hA
    change P.cHf (fun v => v.1.2) (fun v => (v.1.1,v.2)) ≤ _ at hcond
    linarith only [hH,hcond,hsum,hm]
  exact hlow.trans (conditional_iid_information p q n)

open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} {Γ : Type uCapitalGamma} [Fintype Ω] [Fintype α] [Fintype Γ]

lemma conditionOn_support (p : FinLaw Ω) (C : Ω → α) (a : α)
    (ha : p.map C a≠0) (ω : Ω) (hω : p.conditionOn C a ω≠0) :
    p ω≠0 ∧ C ω=a := by
  have hh := p.conditionOn_weight C a ω
  have hn := mul_ne_zero ha hω
  rw [hh] at hn
  split_ifs at hn with hc
  · exact ⟨hn,hc⟩
  · exact False.elim (hn rfl)

lemma joint_conditionOn_mix (p : FinLaw Ω) (C : Ω → α) (q : Ω → FinLaw Γ) :
    (p.map C).joint (fun a => (p.conditionOn C a).mix q)=
      (p.joint q).map (fun v => (C v.1,v.2)) := by
  ext ⟨a,v⟩
  rw [joint_mass,mix_mass,Finset.mul_sum]
  conv_rhs => rw [map_mass,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← mul_assoc,conditionOn_weight]
  simp only [joint_mass,Prod.mk.injEq]
  by_cases hc : C ω=a
  · simp only [hc,true_and,ite_true,Finset.sum_ite_eq',Finset.mem_univ]
  · simp only [hc,false_and,ite_false,zero_mul,Finset.sum_const_zero]

lemma mix_support (p : FinLaw Ω) (q : Ω → FinLaw Γ) (v : Γ)
    (hv : p.mix q v≠0) : ∃ ω, p ω≠0 ∧ q ω v≠0 := by
  rw [mix_mass] at hv
  obtain ⟨ω,_,hω⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  exact ⟨ω,(mul_ne_zero_iff.mp hω)⟩

lemma expected_log_card_passingList_le {G : Type uGroup} [Fintype G]
    (q : FinLaw Γ) (hit : Γ → G → Prop) (x : G)
    (htrue : ∀ v, q v≠0 → ¬hit v x) (n : ℕ) :
    (∑ v, q.iid n v*Real.log (passingList hit n v).card) ≤ Real.log (Fintype.card G) := by
  have hh (v : Fin n → Γ) : q.iid n v*Real.log (passingList hit n v).card ≤
      q.iid n v*Real.log (Fintype.card G) := by
    by_cases hv : q.iid n v=0
    · simp only [hv,zero_mul,le_refl]
    · apply mul_le_mul_of_nonneg_left _ ((q.iid n).nonneg v)
      apply Real.log_le_log
      · exact_mod_cast Finset.card_pos.mpr ⟨x,q.passingList_true hit x htrue n v hv⟩
      · exact_mod_cast Finset.card_le_univ (passingList hit n v)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hh v)
  simpa only [← Finset.sum_mul,(q.iid n).sum_one,one_mul] using hs

lemma cIf_map {β : Type uBeta} {γ : Type uGamma} {δ : Type uDelta} (p : FinLaw Ω) (F : Ω → α)
    (X : α → β) (Y : α → γ) (Z : α → δ) :
    (p.map F).cIf X Y Z=p.cIf (X ∘ F) (Y ∘ F) (Z ∘ F) := by
  unfold cIf
  rw [cHf_map,cHf_map]
  rfl

theorem posterior_passing_information_lower {ι : Type uIota} {O : Type uOutput} [Fintype ι] [Fintype O]
    (G : ι → Type uGroup) [∀ i, Fintype (G i)]
    (p : FinLaw Ω) (old : Ω → O) (X : Ω → ∀ i, G i) (q : Ω → FinLaw Γ)
    (hit : (i : ι) → Γ → G i → Prop) (Good : ι → Ω → Prop)
    (E : (i : ι) → Ω → Finset (G i)) (e c : ι → ℝ) {A H η : ℝ} (n : ℕ)
    (hA : 0≤A) (he : ∀ i, 0≤e i) (hc : ∀ i, 0≤c i)
    (htrue : ∀ ω, p ω≠0 → ∀ v, q ω v≠0 → ∀ i, ¬hit i v (X ω i))
    (hE : ∀ i ω, Good i ω → ((E i ω).card:ℝ)≤e i)
    (hhit : ∀ i ω, Good i ω → ∀ x∉E i ω, c i≤(q ω).prob (fun v => hit i v x))
    (hH : (∑ i, Real.log (Fintype.card (G i)))-H ≤ p.cHf X old)
    (hBad : (∑ i, p.prob (fun ω => ¬Good i ω))≤η)
    (hnum : ∀ i, Real.log (4*e i+(Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*(c i/4))) ≤
      Real.log (Fintype.card (G i))-A) :
    A*((Fintype.card ι:ℝ)-2*η)-H ≤
      (n:ℝ)*(p.joint q).cIf (fun v => X v.1) Prod.snd (fun v => old v.1) := by
  let C := fun ω => (old ω,X ω)
  let μ := p.map C
  let Q := fun a => (p.conditionOn C a).mix q
  let Bad := fun i a => (1/2:ℝ)<(p.conditionOn C a).prob (fun ω => ¬Good i ω)
  have hsurv (a : O × (∀ i, G i)) (ha : μ a≠0) (v : Γ) (hv : Q a v≠0) (i : ι) :
      ¬hit i v (a.2 i) := by
    obtain ⟨ω,hω,hv⟩ := (p.conditionOn C a).mix_support q v hv
    have hw := p.conditionOn_support C a ha ω hω
    have hx : X ω=a.2 := congrArg Prod.snd hw.2
    rw [← hx]
    exact htrue ω hw.1 v hv i
  have hH' : (∑ i, Real.log (Fintype.card (G i)))-H ≤ μ.cHf Prod.snd Prod.fst := by
    rw [cHf_map]
    exact hH
  have hBad' : (∑ i, μ.prob (Bad i))≤2*η := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      p.posterior_unfavorable C (fun ω => ¬Good i ω))
    simp only [← Finset.mul_sum] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hBad (by norm_num))
  have hlist (a : O × (∀ i, G i)) (ha : μ a≠0) (i : ι) :
      (∑ v, (Q a).iid n v*Real.log (passingList (hit i) n v).card) ≤
        Real.log (Fintype.card (G i))-A*(if Bad i a then 0 else 1) := by
    by_cases hb : Bad i a
    · rw [ite_eq_left hb,mul_zero,sub_zero]
      exact (Q a).expected_log_card_passingList_le (hit i) (a.2 i)
        (fun v hv => hsurv a ha v hv i) n
    · rw [ite_eq_right hb,mul_one]
      have hg : (1/2:ℝ)≤(p.conditionOn C a).prob (Good i) := by
        have hh := (p.conditionOn C a).prob_compl (Good i)
        dsimp only [Bad] at hb
        push Not at hb
        linarith only [hh,hb]
      let F := Finset.univ.filter (fun x : G i =>
        (p.conditionOn C a).prob (fun ω => Good i ω ∧ x∉E i ω)<1/4)
      have hf : (F.card:ℝ)≤4*e i :=
        (p.conditionOn C a).mixed_exception_card (Good i) (E i) (he i) (hE i) hg
      have hm (x : G i) (hx : x∉F) : c i/4≤(Q a).prob (fun v => hit i v x) := by
        apply (p.conditionOn C a).mixed_floor q (Good i) (E i) (hit i) (hc i) (hhit i) x
        have hh : ¬(p.conditionOn C a).prob (fun ω => Good i ω ∧ x∉E i ω)<1/4 := by
          simpa only [F,Finset.mem_filter,Finset.mem_univ,true_and] using hx
        exact le_of_not_gt hh
      have ht := (Q a).expected_log_card_passingList (hit i) (a.2 i)
        (fun v hv => hsurv a ha v hv i) F hm n
      have hpos : (0:ℝ)<(Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*(c i/4)) := by
        have hcard : 0<Fintype.card (G i) := Fintype.card_pos_iff.mpr ⟨a.2 i⟩
        exact mul_pos (by exact_mod_cast hcard) (Real.exp_pos _)
      have hl := Real.log_le_log (by positivity : (0:ℝ)<(F.card:ℝ)+
        (Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*(c i/4)))
        (add_le_add hf (le_refl ((Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*(c i/4)))))
      exact ht.trans (hl.trans (hnum i))
  have hh := passing_information_lower G μ Q hit n hsurv Bad hA hH' hBad' hlist
  have hdist : μ.joint Q=(p.joint q).map (fun v => (C v.1,v.2)) :=
    p.joint_conditionOn_mix C q
  rw [hdist,cIf_map] at hh
  exact hh

end FinLaw
end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat
open scoped BigOperators Classical

abbrev WalkPackage (D : ℝ) (B L : ℕ) := latticeBall (D*B) × (Fin L → latticeBall D)

noncomputable def ForwardKernel.packageSymbol (K : ForwardKernel)
    (z : ℕ → GaussianInt) {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (a L : ℕ) (u : Fin (K.bound+1)) :
    WalkPackage D K.bound L :=
  (K.displacementSymbol z hD hs a u,boundedWord z hs L (a+u.val))

noncomputable def ForwardKernel.packageLaw (K : ForwardKernel)
    (z : ℕ → GaussianInt) {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (a L : ℕ) :
    FinLaw (WalkPackage D K.bound L) :=
  (K.law a).map (K.packageSymbol z hD hs a L)

noncomputable def WalkPackage.prefix {D : ℝ} {B L : ℕ}
    (v : WalkPackage D B L) (l : Fin L) : GaussianInt :=
  v.1.val+∑ j : Fin l.val, (v.2 ⟨j.val,lt_trans j.isLt l.isLt⟩).val

lemma ForwardKernel.packageSymbol_prefix (K : ForwardKernel)
    (z : ℕ → GaussianInt) {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (a L : ℕ) (u : Fin (K.bound+1)) (l : Fin L) :
    (K.packageSymbol z hD hs a L u).prefix l=z (a+u.val+l.val)-z a := by
  change z (a+u.val)-z a+(∑ j : Fin l.val, incrementWord z l.val (a+u.val) j)=_
  rw [incrementWord_sum]
  abel

noncomputable def WalkPackage.Hits {D : ℝ} {B L : ℕ}
    (π : GaussianInt) (v : WalkPackage D B L) (x : GaussianInt ⧸ multiples π) : Prop :=
  ∃ l : Fin L, gaussianResidue π (v.prefix l) = -x

lemma ForwardKernel.package_true_survives (K : ForwardKernel)
    (π : GaussianInt) (z : ℕ → GaussianInt) (havoid : ∀ t, ¬π∣z t)
    {D : ℝ} (hD : 0≤D) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (a L : ℕ) :
    ∀ v, K.packageLaw z hD hs a L v≠0 → ¬WalkPackage.Hits π v (gaussianResidue π (z a)) := by
  intro v hv
  rw [packageLaw,FinLaw.map_mass] at hv
  obtain ⟨u,_,hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  have he : K.packageSymbol z hD hs a L u=v := by
    by_contra he
    simp only [ite_eq_right he,ne_self_iff_false] at hu
  rw [← he]
  simpa only [WalkPackage.Hits,K.packageSymbol_prefix] using true_residue_no_hit π z havoid a (a+u.val) L

lemma FinLaw.mass_map_eq_prob {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω] [Fintype α]
    (p : FinLaw Ω) (f : Ω → α) (x : α) : p.map f x=p.prob (fun ω => f ω=x) := rfl

theorem ForwardKernel.smoothed_package_floor (R : ForwardKernel)
    (π : GaussianInt) (z : ℕ → GaussianInt) (hz : Function.Injective z)
    {D τ : ℝ} (hD : 0≤D) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    {L N : ℕ} (hshort : (D*L)^2<(π.norm:ℝ)) (hLN : L≤N)
    (herr : (L:ℝ)/(N+1)≤τ/2) (a : ℕ) (x : GaussianInt ⧸ multiples π)
    (hfloor : τ≤((R.then (smoothingKernel N)).law a).prob
      (fun u => gaussianResidue π (z (a+u.val)-z a) = -x)) :
    (L:ℝ)*τ/2≤((R.then (smoothingKernel N)).packageLaw z hD hs a L).prob
      (fun v => WalkPackage.Hits π v x) := by
  have hf : τ≤((R.law a).joint (fun _ => FinLaw.uniform (Fin (N+1)))).prob
      (fun v => gaussianResidue π (z (a+v.1.val+v.2.val)-z a) = -x) := by
    change τ≤(((R.law a).joint (fun _ => FinLaw.uniform (Fin (N+1)))).map (addOffsets R.bound N)).prob
      (fun (u : Fin (R.bound+N+1)) => gaussianResidue π (z (a+u.val)-z a) = -x) at hfloor
    rw [FinLaw.prob_map] at hfloor
    simpa only [addOffsets,Nat.add_assoc] using hfloor
  have hh := smoothed_package_hit_lower (R.law a) π z hz hD hs hshort hLN herr a
    (fun u => a+u.val) (-x) hf
  rw [packageLaw,FinLaw.prob_map]
  simp only [WalkPackage.Hits,packageSymbol_prefix]
  change _≤(((R.law a).joint (fun _ => FinLaw.uniform (Fin (N+1)))).map (addOffsets R.bound N)).prob
    (fun (u : Fin (R.bound+N+1)) => ∃ l : Fin L, gaussianResidue π (z (a+u.val+l.val)-z a) = -x)
  rw [FinLaw.prob_map]
  simpa only [addOffsets,Nat.add_assoc] using hh

noncomputable def ForwardKernel.passingException (K : ForwardKernel)
    (s : SplitSieve) (z : ℕ → GaussianInt) (a : ℕ) (i : s.SignedIndex) (τ : ℝ) :
    Finset (s.Residue i) := ((K.relativeResidueLaw s z a i).lowResidues τ).image Neg.neg

lemma ForwardKernel.passingException_card (K : ForwardKernel)
    (s : SplitSieve) (z : ℕ → GaussianInt) (a : ℕ) (i : s.SignedIndex) (τ : ℝ) :
    (K.passingException s z a i τ).card=((K.relativeResidueLaw s z a i).lowResidues τ).card := by
  apply Finset.card_image_of_injective
  exact neg_injective

lemma ForwardKernel.not_mem_passingException (K : ForwardKernel)
    (s : SplitSieve) (z : ℕ → GaussianInt) (a : ℕ) (i : s.SignedIndex) (τ : ℝ) (x : s.Residue i)
    (hx : x∉K.passingException s z a i τ) :
    τ/(s.signedPrime i:ℝ)≤(K.relativeResidueLaw s z a i) (-x) := by
  have hh : -x∉(K.relativeResidueLaw s z a i).lowResidues τ := by
    intro h
    exact hx (Finset.mem_image.mpr ⟨-x,h,neg_neg x⟩)
  have he := (K.relativeResidueLaw s z a i).not_mem_lowResidues τ (-x) |>.mp hh
  simpa only [s.residue_card] using he

lemma SplitSieve.avoids_signed (s : SplitSieve) (z : GaussianInt)
    (h : z∈s.avoiding) (i : s.SignedIndex) : ¬s.signedFactorAt i∣z := by
  have hh := h (s.signedPrime i) (s.enumeration i.2).property
  rcases i with ⟨σ,i⟩
  change ¬signedFactor _ (σ i)∣z
  cases he : σ i <;> simp only [signedFactor] <;> tauto

theorem smoothed_batch_package_information {Ω : Type uOmega} {O : Type uOutput} {ι : Type uIota}
    [Fintype Ω] [Fintype O] [Fintype ι]
    (s : SplitSieve) (p : FinLaw Ω) (a : Ω → ℕ) (old : Ω → O)
    (I : ι → s.SignedIndex) (R : ForwardKernel)
    (z : ℕ → GaussianInt) (hz : Function.Injective z)
    (ha : ∀ t, z t∈s.avoiding) {D τ A H η : ℝ} {L N n : ℕ}
    (hD : 0≤D) (hτ : 0≤τ) (hA : 0≤A)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (e : ι → ℝ) (he : ∀ i, 0≤e i)
    (hshort : ∀ i, (D*L)^2<(s.signedPrime (I i):ℝ)) (hLN : L≤N)
    (herr : ∀ i, (L:ℝ)/(N+1)≤(τ/(s.signedPrime (I i):ℝ))/2)
    (hH : (∑ i, Real.log (s.signedPrime (I i)))-H ≤
      p.cHf (fun ω i => s.residue (I i) (z (a ω))) old)
    (hBad : (∑ i, p.prob (fun ω => e i≤
      (((R.then (smoothingKernel N)).relativeResidueLaw s z (a ω) (I i)).lowResidues τ).card))≤η)
    (hnum : ∀ i, Real.log (4*e i+(s.signedPrime (I i):ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.signedPrime (I i):ℝ))/2)/4))) ≤
        Real.log (s.signedPrime (I i))-A) :
    A*((Fintype.card ι:ℝ)-2*η)-H ≤ (n:ℝ)*
      (p.joint (fun ω => (R.then (smoothingKernel N)).packageLaw z hD hs (a ω) L)).cIf
        (fun v i => s.residue (I i) (z (a v.1))) Prod.snd (fun v => old v.1) := by
  let K := R.then (smoothingKernel N)
  let q := fun ω => K.packageLaw z hD hs (a ω) L
  let Good := fun i ω =>
    (((K.relativeResidueLaw s z (a ω) (I i)).lowResidues τ).card:ℝ)<e i
  apply FinLaw.posterior_passing_information_lower (fun i => s.Residue (I i)) p old
    (fun ω i => s.residue (I i) (z (a ω))) q (fun i => WalkPackage.Hits (s.signedFactorAt (I i)))
    Good (fun i ω => K.passingException s z (a ω) (I i) τ) e
    (fun i => (L:ℝ)*(τ/(s.signedPrime (I i):ℝ))/2) n hA he
  · intro i
    positivity
  · intro ω _ v hv i
    exact K.package_true_survives (s.signedFactorAt (I i)) z
      (fun t => s.avoids_signed (z t) (ha t) (I i)) hD hs (a ω) L v hv
  · intro i ω hg
    rw [ForwardKernel.passingException_card]
    exact hg.le
  · intro i ω _ x hx
    apply R.smoothed_package_floor (s.signedFactorAt (I i)) z hz hD hs
      (by simpa only [s.signedFactorAt_norm,Int.cast_natCast] using hshort i) hLN (herr i) (a ω) x
    have hh := K.not_mem_passingException s z (a ω) (I i) τ x hx
    simpa only [ForwardKernel.relativeResidueLaw,FinLaw.mass_map_eq_prob,SplitSieve.residue] using hh
  · simpa only [s.residue_card] using hH
  · simpa only [Good,not_lt] using hBad
  · simpa only [s.residue_card] using hnum

namespace FinLaw
lemma cIf_congr_fibers {Ω : Type uOmega} {α : Type uAlpha} {α' : Type uAlphaPrime} {β : Type uBeta} {β' : Type uBetaPrime} {γ : Type uGamma} {γ' : Type uGammaPrime} [Fintype Ω]
    (p : FinLaw Ω) (X : Ω → α) (X' : Ω → α')
    (Y : Ω → β) (Y' : Ω → β') (O : Ω → γ) (O' : Ω → γ')
    (hX : ∀ ω ν, X ω=X ν ↔ X' ω=X' ν)
    (hY : ∀ ω ν, Y ω=Y ν ↔ Y' ω=Y' ν)
    (hO : ∀ ω ν, O ω=O ν ↔ O' ω=O' ν) :
    p.cIf X Y O=p.cIf X' Y' O' := by
  unfold cIf
  rw [p.cHf_congr_fibers X X' O O' hX hO]
  congr 1
  apply p.cHf_congr_fibers _ _ _ _ hX
  intro ω ν
  simp only [Prod.mk.injEq,hO,hY]

lemma joint_map_cIf {Ω : Type uOmega} {Γ : Type uCapitalGamma} {Γ' : Type uCapitalGammaPrime} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω] [Fintype Γ] [Fintype Γ']
    (p : FinLaw Ω) (q : Ω → FinLaw Γ) (f : Ω → Γ → Γ') (X : Ω → α) (O : Ω → β) :
    (p.joint (fun ω => (q ω).map (f ω))).cIf (fun v => X v.1) Prod.snd (fun v => O v.1)=
      (p.joint q).cIf (fun v => X v.1) (fun v => f v.1 v.2) (fun v => O v.1) := by
  rw [← joint_map_fiber,cIf_map]
  rfl
end FinLaw

theorem ForwardKernel.package_information_transport {Ω : Type uOmega} {ι : Type uIota} {κ : Type uKappa} [Fintype Ω]
    (K : ForwardKernel) (p : FinLaw Ω) (a : Ω → ℕ) (f : ι → GaussianInt) (g : κ → GaussianInt)
    (z : ℕ → GaussianInt) {D : ℝ} (hD : 1≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (hK : 1≤K.bound) (L : ℕ) :
    (p.joint (fun ω => K.packageLaw z (by linarith only [hD]) hs (a ω) L)).cIf
      (fun v i => residueCode (f i) (z (a v.1))) Prod.snd
      (fun v i => residueCode (g i) (z (a v.1))) ≤
    (p.joint (fun ω => K.law (a ω))).cIf
      (fun v i => residueCode (f i) (z (a v.1+v.2.val)))
      (fun v => incrementWord z L (a v.1+v.2.val))
      (fun v i => residueCode (g i) (z (a v.1+v.2.val)))+
      2*(Real.log 36+2*Real.log (D*K.bound)) := by
  let P := p.joint (fun ω => K.law (a ω))
  let X := fun v : Ω × Fin (K.bound+1) => z (a v.1)
  let Y := fun v : Ω × Fin (K.bound+1) => z (a v.1+v.2.val)
  let S := fun v => Y v-X v
  let W := fun v : Ω × Fin (K.bound+1) => incrementWord z L (a v.1+v.2.val)
  have hemap := FinLaw.joint_map_cIf p (fun ω => K.law (a ω))
    (fun ω => K.packageSymbol z (by linarith only [hD]) hs (a ω) L)
    (fun ω i => residueCode (f i) (z (a ω))) (fun ω i => residueCode (g i) (z (a ω)))
  change (p.joint (fun ω => K.packageLaw z (by linarith only [hD]) hs (a ω) L)).cIf _ _ _=_ at hemap
  rw [hemap]
  have he := P.cIf_congr_fibers
    (fun v i => residueCode (f i) (X v)) (fun v i => residueCode (f i) (X v))
    (fun v => K.packageSymbol z (by linarith only [hD]) hs (a v.1) L v.2)
    (fun v => (S v,W v))
    (fun v i => residueCode (g i) (X v)) (fun v i => residueCode (g i) (X v))
    (fun _ _ => Iff.rfl) (fun v w => by
      simp only [ForwardKernel.packageSymbol,Prod.mk.injEq,Subtype.mk.injEq,
        ForwardKernel.displacementSymbol,boundedWord_fibers]
      rfl) (fun _ _ => Iff.rfl)
  change P.cIf _ _ _≤_
  rw [he]
  have ht := P.cIf_transport (fun v i => residueCode (f i) (X v))
    (fun v i => residueCode (g i) (X v)) (fun v i => residueCode (f i) (Y v))
    (fun v i => residueCode (g i) (Y v)) W S
    (residue_observation_shift g X Y) (by
      intro v w
      have hf := residue_observation_shift f X Y v w
      have hg := residue_observation_shift g X Y v w
      simp only [Prod.mk.injEq,S] at hf hg ⊢
      tauto)
  have hc : P.Hf S≤Real.log 36+2*Real.log (D*K.bound) := by
    apply displacement_entropy_le
    · exact one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast hK)
    · intro v
      simpa only [S,X,Y,Nat.add_zero] using walk_pair_displacement z (by linarith only [hD]) hs
        (a v.1) K.bound v.2.val 0 (by omega) (by omega)
  exact ht.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (show (0:ℝ)≤2 by norm_num)))

lemma perm_expect_uniform {ι : Type uIota} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : ι → ℝ) (i : ι) :
    (𝔼 π : Equiv.Perm ι, f (π i))=𝔼 j, f j := by
  have hf (π : Equiv.Perm ι) : (𝔼 j, f (π j))=𝔼 j, f j := by
    rw [Fintype.expect_eq_sum_div_card,Fintype.expect_eq_sum_div_card,Equiv.sum_comp π]
  calc
    _ = 𝔼 j : ι, 𝔼 π : Equiv.Perm ι, f (π j) := by
      simp_rw [← perm_expect_exchange f i]
      rw [Fintype.expect_const]
    _ = 𝔼 π : Equiv.Perm ι, 𝔼 j, f (π j) := Finset.expect_comm _ _ _
    _ = _ := by simp_rw [hf]; rw [Fintype.expect_const]

noncomputable def SplitSieve.selectedIndex (s : SplitSieve) {b : ℕ} (hb : b≤ s.primes.card)
    (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) (j : Fin b) :
    s.SignedIndex := (σ,π ⟨j.val,lt_of_lt_of_le j.isLt hb⟩)

lemma SplitSieve.selected_sum_average (s : SplitSieve) (hne : s.primes.Nonempty)
    {b : ℕ} (hb : b≤ s.primes.card) (f : s.SignedIndex → ℝ) :
    (𝔼 σ : Fin s.primes.card → Bool, 𝔼 π : Equiv.Perm (Fin s.primes.card),
      ∑ j : Fin b, f (s.selectedIndex hb σ π j)) =
    (b:ℝ)*(𝔼 i : s.SignedIndex, f i) := by
  have : Nonempty (Fin s.primes.card) := ⟨⟨0,hne.card_pos⟩⟩
  have hf (σ : Fin s.primes.card → Bool) (j : Fin b) :
      (𝔼 π : Equiv.Perm (Fin s.primes.card),f (s.selectedIndex hb σ π j))=
        𝔼 i : Fin s.primes.card, f (σ,i) := by
    exact perm_expect_uniform (fun i => f (σ,i)) ⟨j.val,lt_of_lt_of_le j.isLt hb⟩
  simp only [Finset.expect_sum_comm,hf,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,← Finset.mul_expect,← Finset.univ_product_univ,Finset.expect_product]

lemma selected_prefix_fibers {Ω : Type uOmega} {α : Type uAlpha} {k b : ℕ} (hb : b≤k)
    (X : Ω → Fin k → α) (π : Equiv.Perm (Fin k)) (ω ν : Ω) :
    (fun j : Fin b => X ω (π ⟨j.val,lt_of_lt_of_le j.isLt hb⟩))=
      (fun j : Fin b => X ν (π ⟨j.val,lt_of_lt_of_le j.isLt hb⟩)) ↔
    FinLaw.prefixVar X π b ω=FinLaw.prefixVar X π b ν := by
  constructor
  · intro h
    funext i
    by_cases hi : i.val<b
    · have hh := congrFun h ⟨i.val,hi⟩
      simpa only [FinLaw.prefixVar,hi,ite_true,Option.some.injEq] using hh
    · simp only [FinLaw.prefixVar,hi,ite_false]
  · intro h
    funext j
    have hh := congrFun h ⟨j.val,lt_of_lt_of_le j.isLt hb⟩
    simpa only [FinLaw.prefixVar,j.isLt,ite_true,Option.some.injEq] using hh

lemma SplitSieve.selected_residue_fibers {Ω : Type uOmega} (s : SplitSieve)
    {b : ℕ} (hb : b≤ s.primes.card) (σ : Fin s.primes.card → Bool)
    (π : Equiv.Perm (Fin s.primes.card)) (Z : Ω → GaussianInt) (ω ν : Ω) :
    (fun j => s.residue (s.selectedIndex hb σ π j) (Z ω))=
      (fun j => s.residue (s.selectedIndex hb σ π j) (Z ν)) ↔
    FinLaw.prefixVar (fun v => s.residueVector σ (Z v)) π b ω=
      FinLaw.prefixVar (fun v => s.residueVector σ (Z v)) π b ν := by
  rw [funext_iff]
  simp only [s.residue_fibers]
  change (∀ j : Fin b, s.residueVector σ (Z ω) (π ⟨j.val,_⟩)=
    s.residueVector σ (Z ν) (π ⟨j.val,_⟩)) ↔ _
  rw [← funext_iff]
  exact selected_prefix_fibers hb (fun v => s.residueVector σ (Z v)) π ω ν

lemma SplitSieve.selected_entropy_average {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve) (p : FinLaw Ω) (Z : Ω → GaussianInt)
    {b : ℕ} (hb : b≤ s.primes.card) :
    (𝔼 σ : Fin s.primes.card → Bool, 𝔼 π : Equiv.Perm (Fin s.primes.card),
      p.Hf (fun ω j => s.residue (s.selectedIndex hb σ π j) (Z ω)))=
    s.pointEntropy p Z b := by
  have h (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) :=
    p.Hf_eq_of_fibers _ _ (s.selected_residue_fibers hb σ π Z)
  simp only [h,SplitSieve.pointEntropy,FinLaw.signedEntropy,FinLaw.orderedEntropy]

lemma SplitSieve.selected_log_average (s : SplitSieve) (hne : s.primes.Nonempty)
    {b : ℕ} (hb : b≤ s.primes.card) :
    (𝔼 σ : Fin s.primes.card → Bool, 𝔼 π : Equiv.Perm (Fin s.primes.card),
      ∑ j : Fin b, Real.log (s.signedPrime (s.selectedIndex hb σ π j))) =
    (b:ℝ)*s.meanLog := by
  rw [s.selected_sum_average hne hb (fun i => Real.log (s.signedPrime i))]
  simp only [← Finset.univ_product_univ,Finset.expect_product,
    SplitSieve.signedPrime,Fintype.expect_const,SplitSieve.meanLog]

theorem averaged_batch_package_information {Ω : Type uOmega} {O : Type uOutput} [Fintype Ω] [Fintype O]
    (s : SplitSieve) (hne : s.primes.Nonempty) (p : FinLaw Ω) (a : Ω → ℕ)
    (old : Ω → O) (R : ForwardKernel) (z : ℕ → GaussianInt)
    (hz : Function.Injective z) (ha : ∀ t, z t∈s.avoiding)
    {b L N n : ℕ} (hb : b≤ s.primes.card) {D τ A η δ E : ℝ}
    (hD : 0≤D) (hτ : 0≤τ) (hA : 0≤A)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (e : s.SignedIndex → ℝ) (he : ∀ i, 0≤e i)
    (hshort : ∀ i, (D*L)^2<(s.signedPrime i:ℝ)) (hLN : L≤N)
    (herr : ∀ i, (L:ℝ)/(N+1)≤(τ/(s.signedPrime i:ℝ))/2)
    (hH : (1-δ)*(b:ℝ)*s.meanLog≤ s.pointEntropy p (fun ω => z (a ω)) b)
    (hO : p.Hf old≤E)
    (hBad : (𝔼 i : s.SignedIndex, p.prob (fun ω => e i≤
      (((R.then (smoothingKernel N)).relativeResidueLaw s z (a ω) i).lowResidues τ).card))≤η)
    (hnum : ∀ i, Real.log (4*e i+(s.signedPrime i:ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.signedPrime i:ℝ))/2)/4))) ≤
        Real.log (s.signedPrime i)-A) :
    (b:ℝ)*(A*(1-2*η)-δ*s.meanLog)-E ≤ (n:ℝ)*
      (𝔼 σ : Fin s.primes.card → Bool, 𝔼 π : Equiv.Perm (Fin s.primes.card),
        (p.joint (fun ω => (R.then (smoothingKernel N)).packageLaw z hD hs (a ω) L)).cIf
          (fun v j => s.residue (s.selectedIndex hb σ π j) (z (a v.1)))
          Prod.snd (fun v => old v.1)) := by
  let X := fun (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card))
    (ω : Ω) (j : Fin b) => s.residue (s.selectedIndex hb σ π j) (z (a ω))
  let Bad := fun i => p.prob (fun ω => e i≤
    (((R.then (smoothingKernel N)).relativeResidueLaw s z (a ω) i).lowResidues τ).card)
  have hi (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) :=
    smoothed_batch_package_information s p a old (s.selectedIndex hb σ π) R z hz ha
      hD hτ hA hs (fun j => e (s.selectedIndex hb σ π j))
      (fun j => he _) (fun j => hshort _) hLN (fun j => herr _)
      (H := (∑ j, Real.log (s.signedPrime (s.selectedIndex hb σ π j)))-p.cHf (X σ π) old)
      (by dsimp only [X]; linarith)
      (η := ∑ j, Bad (s.selectedIndex hb σ π j)) le_rfl (fun j => hnum _)
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ => hi σ π))
  simp only [Fintype.card_fin,Finset.expect_sub_distrib,← Finset.mul_expect,Fintype.expect_const,
    Finset.expect_sum_comm] at hav
  have hx (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) :
      p.Hf (X σ π)-E≤p.cHf (X σ π) old := by
    have h := p.Hf_pair_ge_snd old (X σ π)
    rw [p.Hf_pair_comm] at h
    unfold FinLaw.cHf
    linarith only [h,hO]
  have hxa := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ => hx σ π))
  simp only [Finset.expect_sub_distrib,Fintype.expect_const] at hxa
  have hxe := s.selected_entropy_average p (fun ω => z (a ω)) hb
  change (𝔼 σ, 𝔼 π, p.Hf (X σ π))=_ at hxe
  rw [hxe] at hxa
  have hlog := s.selected_log_average hne hb
  have hbad := s.selected_sum_average hne hb Bad
  have hbR : 0≤(b:ℝ) := Nat.cast_nonneg _
  have hbadle : (b:ℝ)*(𝔼 i, Bad i)≤b*η := mul_le_mul_of_nonneg_left hBad hbR
  simp only [Finset.expect_sum_comm] at hlog hbad
  rw [hlog,hbad] at hav
  have hprod := mul_le_mul_of_nonneg_left hbadle hA
  linarith only [hav,hxa,hH,hprod]

end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat
open scoped BigOperators Classical

theorem exists_batch_information {Ω : Type uOmega} {κ : Type uKappa} [Fintype Ω]
    (s : SplitSieve) (hne : s.primes.Nonempty) (p : FinLaw Ω) (a : Ω → ℕ)
    (g : κ → GaussianInt) (R : ForwardKernel) (z : ℕ → GaussianInt)
    (hz : Function.Injective z) (ha : ∀ t, z t∈s.avoiding)
    {b L N n : ℕ} (hb : b≤ s.primes.card) (hn : 0<n) (hL : 0<L)
    {D τ A η δ E r : ℝ} (hD : 1≤D) (hτ : 0≤τ) (hA : 0≤A)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (e : s.SignedIndex → ℝ) (he : ∀ i, 0≤e i)
    (hshort : ∀ i, (D*L)^2<(s.signedPrime i:ℝ)) (hLN : L≤N)
    (herr : ∀ i, (L:ℝ)/(N+1)≤(τ/(s.signedPrime i:ℝ))/2)
    (hH : (1-δ)*(b:ℝ)*s.meanLog≤ s.pointEntropy p (fun ω => z (a ω)) b)
    (hO : p.Hf (fun ω i => residueCode (g i) (z (a ω)))≤E)
    (hBad : (𝔼 i : s.SignedIndex, p.prob (fun ω => e i≤
      (((R.then (smoothingKernel N)).relativeResidueLaw s z (a ω) i).lowResidues τ).card))≤η)
    (hnum : ∀ i, Real.log (4*e i+(s.signedPrime i:ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.signedPrime i:ℝ))/2)/4))) ≤
        Real.log (s.signedPrime i)-A)
    (hrate : (n:ℝ)*((L:ℝ)*r+2*(Real.log 36+2*Real.log (D*(R.bound+N)))) ≤
      (b:ℝ)*(A*(1-2*η)-δ*s.meanLog)-E) :
    ∃ σ : Fin s.primes.card → Bool, ∃ π : Equiv.Perm (Fin s.primes.card),
      r≤ (p.joint (fun ω => (R.then (smoothingKernel N)).law (a ω))).cIf
        (fun v j => residueCode (s.signedFactorAt (s.selectedIndex hb σ π j))
          (z (a v.1+v.2.val)))
        (fun v => incrementWord z L (a v.1+v.2.val))
        (fun v i => residueCode (g i) (z (a v.1+v.2.val))) / L := by
  let K := R.then (smoothingKernel N)
  let old := fun ω i => residueCode (g i) (z (a ω))
  let old' := FinLaw.outputCode old
  have hOld : p.Hf old'≤E := by
    apply le_trans (le_of_eq (p.Hf_eq_of_fibers old' old (fun ω ν => FinLaw.outputCode_eq_iff old ω ν))) hO
  have hD0 : 0≤D := by linarith only [hD]
  have hlower := averaged_batch_package_information s hne p a old' R z hz ha hb
    hD0 hτ hA hs e he hshort hLN herr hH hOld hBad hnum
  let Info := fun (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) =>
    (p.joint (fun ω => K.law (a ω))).cIf
      (fun v j => residueCode (s.signedFactorAt (s.selectedIndex hb σ π j)) (z (a v.1+v.2.val)))
      (fun v => incrementWord z L (a v.1+v.2.val))
      (fun v i => residueCode (g i) (z (a v.1+v.2.val)))
  have hK : 1≤K.bound := by change 1≤R.bound+N; omega
  have ht (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) :
      (p.joint (fun ω => K.packageLaw z hD0 hs (a ω) L)).cIf
        (fun v j => s.residue (s.selectedIndex hb σ π j) (z (a v.1))) Prod.snd
        (fun v => old' v.1) ≤ Info σ π+2*(Real.log 36+2*Real.log (D*K.bound)) := by
    have hc := (p.joint (fun ω => K.packageLaw z hD0 hs (a ω) L)).cIf_congr_fibers
      (fun v j => s.residue (s.selectedIndex hb σ π j) (z (a v.1)))
      (fun v j => residueCode (s.signedFactorAt (s.selectedIndex hb σ π j)) (z (a v.1)))
      Prod.snd Prod.snd (fun v => old' v.1) (fun v => old v.1)
      (fun v w => by
        simp only [funext_iff,SplitSieve.residue,gaussianResidue_eq,residueCode_eq])
      (fun _ _ => Iff.rfl) (fun v w => FinLaw.outputCode_eq_iff old v.1 w.1)
    rw [hc]
    exact K.package_information_transport p a (fun j => s.signedFactorAt (s.selectedIndex hb σ π j))
      g z hD hs hK L
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ => ht σ π))
  simp only [Finset.expect_add_distrib,Fintype.expect_const] at hav
  have hmul := mul_le_mul_of_nonneg_left hav (Nat.cast_nonneg n)
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  have hrate' : (L:ℝ)*r≤𝔼 σ, 𝔼 π, Info σ π := by
    have heK : (K.bound:ℝ)=R.bound+N := by simp only [K,ForwardKernel.then,smoothingKernel,Nat.cast_add]
    conv at hmul => rhs; rw [heK]
    have hh := hrate.trans (hlower.trans hmul)
    apply (mul_le_mul_iff_right₀ hnR).mp
    linarith only [hh]
  obtain ⟨σ,_,hσ⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hrate'
  obtain ⟨π,_,hπ⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hσ
  refine ⟨σ,π,?_⟩
  exact (le_div_iff₀ (show (0:ℝ)<L by exact_mod_cast hL)).mpr (by simpa only [mul_comm] using hπ)

lemma finite_entropy_telescope (n : ℕ) (a b : ℕ → ℝ) (ε : ℝ)
    (hnext : ∀ j<n, a (j+1)≤b j+ε) (hb : 0≤b n) :
    (∑ j∈Finset.range (n+1), (a j-b j)) ≤ a 0+n*ε := by
  have h : (∑ j∈Finset.range (n+1), (a j-b j)) ≤ a 0+n*ε-b n := by
    clear hb
    induction n with
    | zero => simp
    | succ n ih =>
      have hn := ih (fun j hj => hnext j (by omega))
      have hh := hnext n (by omega)
      rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
      linarith only [hn,hh]
  linarith only [h,hb]

theorem word_entropy_rate_monotone {Ω : Type uOmega} {ι : Type uIota} [Fintype Ω] [Fintype ι]
    (p : FinLaw Ω) (t : Ω → ℕ) (z : ℕ → GaussianInt) {D : ℝ}
    (hz : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (f : ι → GaussianInt) (hf : ∀ i, f i≠0) {L K N : ℕ}
    (hL : 0<L) (hK : 0<K) (hdiv : L∣K) (hKN : K≤N) {ε : ℝ} (hε : 0≤ε)
    (herr : ∀ a<K, 2*Real.binEntropy ((a:ℝ)/(N+1))+
      ((a:ℝ)/(N+1))*((L:ℝ)*Real.log (latticeBall D).card+
        2*∑ i, Real.log (f i).norm.natAbs) ≤ ε) :
    let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
    P.cHf (fun v => incrementWord z K (t v.1+v.2.val))
      (fun v i => residueCode (f i) (z (t v.1+v.2.val))) / K ≤
    P.cHf (fun v => incrementWord z L (t v.1+v.2.val))
      (fun v i => residueCode (f i) (z (t v.1+v.2.val))) / L + ε := by
  dsimp only
  let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
  let u := fun v : Ω × Fin (N+1) => t v.1+v.2.val
  let Q := fun v i => residueCode (f i) (z (u v))
  let H := P.cHf (fun v => incrementWord z L (u v)) Q
  obtain ⟨m,hm⟩ := hdiv
  have hm' : K=m*L := by simpa [Nat.mul_comm] using hm
  have hmp : 0 < m := by nlinarith only [hK,hm]
  have hLp : (0:ℝ)<L := by exact_mod_cast hL
  have hmR : (0:ℝ) < m := by exact_mod_cast hmp
  have hblock := incrementWord_blocks_entropy P u z f L m hL
  have hsum : (∑ j : Fin m, P.cHf (fun v => incrementWord z L (u v+j.val*L))
      (fun v i => residueCode (f i) (z (u v+j.val*L)))) ≤ (m:ℝ)*(H+ε) := by
    have hh (j : Fin m) : P.cHf (fun v => incrementWord z L (u v+j.val*L))
        (fun v i => residueCode (f i) (z (u v+j.val*L))) ≤ H+ε := by
      have hj : j.val*L<K := by rw [hm']; exact Nat.mul_lt_mul_of_pos_right j.isLt hL
      have hs := word_residue_smoothing p t z hz f hf L N (j.val*L) (by omega)
      dsimp only at hs
      change P.cHf _ _ ≤ H+_+_ at hs
      have he := herr (j.val*L) hj
      linarith only [hs,he]
    have hh' := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hh j)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh'
  have htotal := hblock.trans hsum
  have hd := div_le_div_of_nonneg_right htotal (show (0:ℝ)≤ m*L by positivity)
  have he : (m:ℝ)*(H+ε)/((m:ℝ)*L)=(H+ε)/L := by field_simp
  rw [he,add_div] at hd
  have hel : ε/(L:ℝ)≤ε := div_le_self hε (by exact_mod_cast hL)
  rw [hm',Nat.cast_mul]
  change P.cHf (fun v => incrementWord z (m*L) (u v)) Q / ((m:ℝ)*L) ≤ H/L+ε
  linarith only [hd,hel]

lemma FinLaw.cIf_refinement {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} [Fintype Ω]
    (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (O : Ω → γ)
    (h : ∀ ω ν, X ω = X ν → O ω = O ν) :
    p.cIf X Y O = p.cHf Y O - p.cHf Y X := by
  rw [p.cIf_comm]
  unfold FinLaw.cIf
  congr 1
  apply p.cHf_congr_fibers Y Y (fun ω => (O ω,X ω)) X
  · intro ω ν; rfl
  · intro ω ν
    simp only [Prod.mk.injEq]
    exact ⟨And.right,fun hx => ⟨h ω ν hx,hx⟩⟩

theorem common_law_information_telescope {Ω : Type uOmega} [Fintype Ω]
    (p : FinLaw Ω) (t : Ω → ℕ) (z : ℕ → GaussianInt) {D : ℝ}
    (hz : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    (F : ℕ → Finset GaussianInt) (hF : ∀ j, F j ⊆ F (j+1))
    (hf : ∀ j, ∀ f ∈ F j, f ≠ 0) (L : ℕ → ℕ) (n N : ℕ)
    (hL : ∀ j ≤ n, 0 < L j) (hdiv : ∀ j < n, L j ∣ L (j+1))
    (hN : ∀ j ≤ n, L j ≤ N) {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ j < n, ∀ a < L (j+1),
      2*Real.binEntropy ((a:ℝ)/(N+1)) + ((a:ℝ)/(N+1))*
        ((L j:ℝ)*Real.log (latticeBall D).card +
          2*∑ f ∈ F (j+1), Real.log f.norm.natAbs) ≤ ε) :
    let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
    let u := fun v : Ω × Fin (N+1) => t v.1+v.2.val
    (∑ j ∈ Finset.range (n+1),
      P.cIf (fun v (f : F (j+1)) => residueCode f.val (z (u v)))
        (fun v => incrementWord z (L j) (u v))
        (fun v (f : F j) => residueCode f.val (z (u v))) / L j) ≤
      Real.log (latticeBall D).card + n*ε := by
  dsimp only
  let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
  let u := fun v : Ω × Fin (N+1) => t v.1+v.2.val
  let Q := fun j => fun v (f : F j) => residueCode f.val (z (u v))
  let a := fun j => P.cHf (fun v => incrementWord z (L j) (u v)) (Q j) / L j
  let b := fun j => P.cHf (fun v => incrementWord z (L j) (u v)) (Q (j+1)) / L j
  have hnext (j : ℕ) (hj : j < n) : a (j+1) ≤ b j+ε := by
    dsimp only [a,b,Q,u,P]
    apply word_entropy_rate_monotone p t z hz (fun f : F (j+1) => f.val)
      (fun f => hf _ _ f.property) (hL j (by omega)) (hL (j+1) (by omega))
      (hdiv j hj) (hN (j+1) (by omega)) hε
    intro k hk
    convert herr j hj k hk using 1
    rw [Finset.sum_coe_sort (F (j+1)) (fun f : GaussianInt => Real.log f.norm.natAbs)]
  have hb : 0 ≤ b n := div_nonneg (P.cHf_nonneg _ _) (Nat.cast_nonneg _)
  have hi (j : ℕ) : P.cIf (Q (j+1)) (fun v => incrementWord z (L j) (u v)) (Q j) /
      L j = a j-b j := by
    rw [P.cIf_refinement,sub_div]
    intro v w hv
    funext f
    exact congrFun hv ⟨f.val,hF j f.property⟩
  have ht := finite_entropy_telescope n a b ε hnext hb
  have ha : a 0 ≤ Real.log (latticeBall D).card := by
    apply (div_le_iff₀ (show (0:ℝ) < L 0 by exact_mod_cast hL 0 (by omega))).mpr
    have hh := (P.cHf_le_Hf (fun v => incrementWord z (L 0) (u v)) (Q 0)).trans
      (boundedWord_entropy_le P u z hz (L 0))
    simpa only [mul_comm] using hh
  change (∑ j ∈ Finset.range (n+1), P.cIf (Q (j+1))
    (fun v => incrementWord z (L j) (u v)) (Q j) / L j) ≤ _
  simp only [hi]
  linarith only [ht,ha]

noncomputable def TimeLaw.info {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} (P : TimeLaw)
    (X : ℕ → α) (Y : ℕ → β) (O : ℕ → γ) : ℝ :=
  P.law.cIf (fun t => X t.val) (fun t => Y t.val) (fun t => O t.val)

lemma TimeLaw.advance_info {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} (P : TimeLaw) (K : ForwardKernel)
    (X : ℕ → α) (Y : ℕ → β) (O : ℕ → γ) :
    (P.advance K).info X Y O=(P.law.joint (fun a => K.law a.val)).cIf
      (fun v => X (v.1.val+v.2.val)) (fun v => Y (v.1.val+v.2.val))
      (fun v => O (v.1.val+v.2.val)) := by
  unfold TimeLaw.info TimeLaw.advance
  rw [FinLaw.cIf_map]
  rfl

lemma commonSchedule_smooth (z : ℕ → GaussianInt) (ns : List ℕ) (N : ℕ) :
    commonSchedule z ns N=(commonSchedule z ns 0).then (smoothingKernel N) := by
  simpa only [List.append_nil,commonSchedule,List.foldr_nil] using commonSchedule_append z ns [] N

theorem schedule_information_telescope (z : ℕ → GaussianInt) {D : ℝ}
    (hz : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (ns : List ℕ) (N n : ℕ)
    (F : ℕ → Finset GaussianInt) (hF : ∀ j, F j⊆F (j+1))
    (hf : ∀ j, ∀ f∈F j, f≠0) (L : ℕ → ℕ)
    (hL : ∀ j≤n, 0<L j) (hdiv : ∀ j<n, L j∣L (j+1)) (hN : ∀ j≤n, L j≤N)
    {ε : ℝ} (hε : 0≤ε)
    (herr : ∀ j<n, ∀ a<L (j+1), 2*Real.binEntropy ((a:ℝ)/(N+1))+
      ((a:ℝ)/(N+1))*((L j:ℝ)*Real.log (latticeBall D).card+
        2*∑ f∈F (j+1), Real.log f.norm.natAbs)≤ε) :
    let P := (TimeLaw.at 0).advance (commonSchedule z ns N)
    (∑ j∈Finset.range (n+1), P.info
      (fun a (f : F (j+1)) => residueCode f.val (z a)) (incrementWord z (L j))
      (fun a (f : F j) => residueCode f.val (z a)) / L j)≤
        Real.log (latticeBall D).card+n*ε := by
  let Q := (TimeLaw.at 0).advance (commonSchedule z ns 0)
  have h := common_law_information_telescope Q.law (fun t => t.val) z hz F hF hf L n N
    hL hdiv hN hε herr
  dsimp only
  rw [commonSchedule_smooth,TimeLaw.advance_then]
  simp only [TimeLaw.advance_info]
  exact h

theorem schedule_batch_information (s : SplitSieve) (hne : s.primes.Nonempty)
    (z : ℕ → GaussianInt) (hz : Function.Injective z) (ha : ∀ t, z t∈s.avoiding)
    (pre rest : List ℕ) {N b L n : ℕ} {D T τ A η δ E r : ℝ}
    (hD : 1≤D) (hT : 5≤T) (hML : 1≤ s.meanLog)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (hpT : ∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T)
    (band : EntropyBand s D pre 0 b δ)
    (u : s.SignedIndex → ℝ) (coverage : CoverageDerivation s D N rest τ u η)
    {κ : Type uKappa} (f : κ → GaussianInt)
    (hOld : ((TimeLaw.at 0).advance (commonSchedule z pre 0)).law.Hf
      (fun t i => residueCode (f i) (z t.val))≤E)
    (hb : b≤ s.primes.card) (hn : 0<n) (hL : 0<L) (hτ : 0≤τ) (hA : 0≤A)
    (hu : ∀ i, 0≤u i) (hshort : ∀ i, (D*L)^2<(s.signedPrime i:ℝ)) (hLN : L≤N)
    (herr : ∀ i, (L:ℝ)/(N+1)≤(τ/(s.signedPrime i:ℝ))/2)
    (hnum : ∀ i, Real.log (4*u i+(s.signedPrime i:ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.signedPrime i:ℝ))/2)/4)))≤Real.log (s.signedPrime i)-A)
    (hrate : (n:ℝ)*((L:ℝ)*r+2*(Real.log 36+2*Real.log (D*(rest.sum+N))))≤
      (b:ℝ)*(A*(1-2*η)-δ*s.meanLog)-E) :
    ∃ σ : Fin s.primes.card → Bool, ∃ π : Equiv.Perm (Fin s.primes.card),
      r≤((TimeLaw.at 0).advance (commonSchedule z (pre++rest) N)).info
        (fun a j => residueCode (s.signedFactorAt (s.selectedIndex hb σ π j)) (z a))
        (incrementWord z L) (fun a i => residueCode (f i) (z a)) / L := by
  let P := (TimeLaw.at 0).advance (commonSchedule z pre 0)
  let R := commonSchedule z rest 0
  have hH : (1-δ)*(b:ℝ)*s.meanLog≤ s.pointEntropy P.law (fun t => z t.val) b := by
    rw [SplitSieve.pointEntropy_exact_start]
    simpa only [Nat.zero_add] using band.sound hne z hz hD hT hs hpT hML 0
  have hc := coverage.sound hne z hz hD hT hs hpT hML
  have hBad : (𝔼 i : s.SignedIndex, P.law.prob (fun ω => u i≤
      (((R.then (smoothingKernel N)).relativeResidueLaw s z ω.val i).lowResidues τ).card))≤η := by
    let := s.signedIndex_nonempty hne
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
      mul_le_mul_of_nonneg_left (hc ω.val) (P.law.nonneg ω))
    simp only [← Finset.sum_mul,P.law.sum_one,one_mul] at hh
    rw [← commonSchedule_smooth]
    unfold FinLaw.prob at hh ⊢
    rw [Finset.expect_eq_sum_div_card]
    simp only [FinLaw.uniform,Finset.mul_sum,mul_ite,mul_zero] at hh
    rw [Finset.sum_comm] at hh
    convert hh using 1
    all_goals first | rfl | simp only [Finset.card_univ,div_eq_mul_inv,Finset.sum_mul,ite_mul,zero_mul]
  obtain ⟨σ,π,hh⟩ := exists_batch_information s hne P.law (fun t => t.val) f R z hz ha
    hb hn hL hD hτ hA hs u hu hshort hLN herr hH hOld hBad hnum
    (by simpa only [R,commonSchedule_bound,Nat.add_zero] using hrate)
  refine ⟨σ,π,?_⟩
  have heR : commonSchedule z rest N=R.then (smoothingKernel N) := commonSchedule_smooth z rest N
  rw [commonSchedule_append,TimeLaw.advance_then,TimeLaw.advance_info,heR]
  exact hh

end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat
open scoped BigOperators Classical

noncomputable def chosenSplitFactor (p : ℕ) : GaussianInt :=
  if h : p.Prime ∧ p%4=1 then (exists_split_factor h.1 h.2).choose else 0

lemma chosenSplitFactor_spec {p : ℕ} (hp : p.Prime) (hm : p%4=1) :
    Irreducible (chosenSplitFactor p) ∧ (chosenSplitFactor p).norm=(p:ℤ) := by
  rw [chosenSplitFactor,dite_eq_left ⟨hp,hm⟩]
  exact (exists_split_factor hp hm).choose_spec

noncomputable def splitSieveOf (S : Finset ℕ)
    (hS : ∀ p∈S, p.Prime ∧ p%4=1) : SplitSieve where
  primes := S
  factor := chosenSplitFactor
  prime_mem := fun p hp => (hS p hp).1
  mod_four := fun p hp => (hS p hp).2
  factor_irreducible := fun p hp => (chosenSplitFactor_spec (hS p hp).1 (hS p hp).2).1
  factor_norm := fun p hp => (chosenSplitFactor_spec (hS p hp).1 (hS p hp).2).2

noncomputable def dyadicSieve (j : ℕ) : SplitSieve :=
  splitSieveOf (PrimeLogMass.dyadicBatch j) (fun p hp => by
    have h := (PrimeLogMass.mem_dyadicBatch j p).mp hp
    exact ⟨h.2.2.1,h.2.2.2⟩)

lemma gaussian_norm_log_nonneg (f : GaussianInt) : 0≤Real.log f.norm.natAbs := by
  by_cases h : f.norm.natAbs=0
  · simp only [h,Nat.cast_zero,Real.log_zero,le_refl]
  · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h)

noncomputable def residueWeight (F : Finset GaussianInt) : ℝ :=
  ∑ f∈F, Real.log f.norm.natAbs

lemma residueWeight_mono {F G : Finset GaussianInt} (h : F⊆G) : residueWeight F≤residueWeight G :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun f _ _ => gaussian_norm_log_nonneg f)

lemma residueWeight_nonneg (F : Finset GaussianInt) : 0≤residueWeight F :=
  Finset.sum_nonneg (fun f _ => gaussian_norm_log_nonneg f)

theorem residue_vector_entropy {Ω : Type uOmega} {ι : Type uIota} [Fintype Ω] [Fintype ι]
    (p : FinLaw Ω) (z : Ω → GaussianInt) (f : ι → GaussianInt) (hf : ∀ i, f i≠0) :
    p.Hf (fun ω i => residueCode (f i) (z ω))≤∑ i, Real.log (f i).norm.natAbs := by
  let (i : ι) : Finite (GaussianInt ⧸ multiples (f i)) := finite_gaussianResidue (hf i)
  let (i : ι) : Fintype (GaussianInt ⧸ multiples (f i)) := Fintype.ofFinite _
  rw [p.Hf_eq_of_fibers _ (fun ω i => gaussianResidue (f i) (z ω))
    (fun ω ν => residueCode_vector_fibers f (z ω) (z ν))]
  have hh := p.Hf_le_log_card_type (fun ω i => gaussianResidue (f i) (z ω))
  rw [Fintype.card_pi,Nat.cast_prod,Real.log_prod] at hh
  · convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← Nat.card_eq_fintype_card,multiples_index (hf i)]
  · intro i _
    exact_mod_cast Fintype.card_ne_zero

lemma residue_finset_entropy {Ω : Type uOmega} [Fintype Ω] (p : FinLaw Ω)
    (z : Ω → GaussianInt) (F : Finset GaussianInt) (hf : ∀ f∈F, f≠0) :
    p.Hf (fun ω (f : F) => residueCode f.val (z ω))≤residueWeight F := by
  have h := residue_vector_entropy p z (fun f : F => f.val) (fun f => hf f.val f.property)
  exact h.trans_eq (Finset.sum_subtype F (fun _ => Iff.rfl)
    (fun f : GaussianInt => Real.log f.norm.natAbs)).symm

noncomputable def SplitSieve.availableFactors (s : SplitSieve) : Finset GaussianInt :=
  Finset.univ.image (fun i : s.primes × Bool => signedFactor (s.factor i.1.val) i.2)

lemma SplitSieve.signed_mem_available (s : SplitSieve) (i : s.SignedIndex) :
    s.signedFactorAt i∈s.availableFactors := by
  exact Finset.mem_image.mpr ⟨(s.enumeration i.2,i.1 i.2),Finset.mem_univ _,rfl⟩

lemma SplitSieve.available_ne_zero (s : SplitSieve) {f : GaussianInt} (hf : f∈s.availableFactors) :
    f≠0 := by
  obtain ⟨⟨p,b⟩,_,rfl⟩ := Finset.mem_image.mp hf
  intro h
  have hn := (signedFactor_norm (s.factor p.val) b).trans (s.factor_norm p.val p.property)
  rw [h] at hn
  have hp := (s.prime_mem p.val p.property).ne_zero
  apply hp
  simpa only [Zsqrtd.norm_zero,Nat.cast_eq_zero] using hn.symm

lemma SplitSieve.available_weight (s : SplitSieve) :
    residueWeight s.availableFactors≤2*∑ p∈s.primes, Real.log (p:ℝ) := by
  have hh := Finset.sum_image_le_of_nonneg (s := (Finset.univ : Finset (s.primes × Bool)))
    (g := fun i : s.primes × Bool => signedFactor (s.factor i.1.val) i.2)
    (f := fun f : GaussianInt => Real.log f.norm.natAbs) (fun f _ => gaussian_norm_log_nonneg f)
  change residueWeight s.availableFactors≤_ at hh
  apply hh.trans_eq
  simp only [Fintype.sum_prod_type,signedFactor_norm]
  simp only [s.factor_norm _ (Subtype.property _),Int.natAbs_natCast]
  simp only [Fintype.sum_bool,Finset.sum_add_distrib]
  rw [← Finset.sum_subtype s.primes (fun _ => Iff.rfl) (fun p : ℕ => Real.log (p:ℝ))]
  ring

lemma FinLaw.cIf_finset_union {Ω : Type uOmega} {ι : Type uIota} {β : Type uBeta} [Fintype Ω] [Fintype ι]
    (p : FinLaw Ω) (z : Ω → GaussianInt) (Y : Ω → β)
    (F : Finset GaussianInt) (f : ι → GaussianInt) :
    p.cIf (fun ω (g : ↥(F∪Finset.univ.image f)) => residueCode g.val (z ω)) Y
      (fun ω (g : F) => residueCode g.val (z ω))=
    p.cIf (fun ω i => residueCode (f i) (z ω)) Y
      (fun ω (g : F) => residueCode g.val (z ω)) := by
  rw [p.cIf_comm,p.cIf_comm (fun ω i => residueCode (f i) (z ω))]
  unfold FinLaw.cIf
  congr 1
  apply p.cHf_congr_fibers
  · intro ω ν; rfl
  · intro ω ν
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨hO,hU⟩
      refine ⟨hO,funext fun i => ?_⟩
      exact congrFun hU ⟨f i,Finset.mem_union_right F (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩
    · rintro ⟨hO,hU⟩
      refine ⟨hO,funext fun g => ?_⟩
      rcases Finset.mem_union.mp g.property with hg|hg
      · exact congrFun hO ⟨g.val,hg⟩
      · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hg
        simpa only [hi] using congrFun hU i

end GaussianMoat

end OAI
end
end

section
section
namespace OAI

namespace GaussianMoat

section
open scoped BigOperators Classical

structure BatchCertificate (D : ℝ) (ns : List ℕ) (N : ℕ) (s : SplitSieve)
    (L : ℕ) (E r : ℝ) where
  pre : List ℕ
  rest : List ℕ
  schedule : ns=pre++rest
  T : ℝ
  nonempty : s.primes.Nonempty
  prime_scale : ∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T
  large : 5≤T
  mean : 1≤ s.meanLog
  b : ℕ
  n : ℕ
  τ : ℝ
  A : ℝ
  η : ℝ
  δ : ℝ
  u : s.SignedIndex → ℝ
  band : EntropyBand s D pre 0 b δ
  coverage : CoverageDerivation s D N rest τ u η
  cap : b≤ s.primes.card
  repetitions : 0<n
  length : 0<L
  floor : 0≤τ
  gain : 0≤A
  exceptions : ∀ i, 0≤u i
  short : ∀ i, (D*L)^2<(s.signedPrime i:ℝ)
  smooth_length : L≤N
  smooth_error : ∀ i, (L:ℝ)/(N+1)≤(τ/(s.signedPrime i:ℝ))/2
  list : ∀ i, Real.log (4*u i+(s.signedPrime i:ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.signedPrime i:ℝ))/2)/4)))≤Real.log (s.signedPrime i)-A
  rate : (n:ℝ)*((L:ℝ)*r+2*(Real.log 36+2*Real.log (D*(rest.sum+N))))≤
      (b:ℝ)*(A*(1-2*η)-δ*s.meanLog)-E

theorem BatchCertificate.sound {D E r : ℝ} {ns : List ℕ} {N L : ℕ} {s : SplitSieve}
    (q : BatchCertificate D ns N s L E r) (hD : 1≤D)
    (z : ℕ → GaussianInt) (hz : Function.Injective z) (ha : ∀ t, z t∈s.avoiding)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (F : Finset GaussianInt) (hf : ∀ f∈F, f≠0) (hF : residueWeight F≤E) :
    ∃ G : Finset GaussianInt, F⊆G ∧ G⊆F∪s.availableFactors ∧
      r≤((TimeLaw.at 0).advance (commonSchedule z ns N)).info
        (fun a (f : G) => residueCode f.val (z a)) (incrementWord z L)
        (fun a (f : F) => residueCode f.val (z a)) / L := by
  let Q := (TimeLaw.at 0).advance (commonSchedule z q.pre 0)
  have hOld : Q.law.Hf (fun t (f : F) => residueCode f.val (z t.val))≤E :=
    (residue_finset_entropy Q.law (fun t => z t.val) F hf).trans hF
  obtain ⟨σ,π,hh⟩ := schedule_batch_information s q.nonempty z hz ha q.pre q.rest hD q.large
    q.mean hs q.prime_scale q.band q.u q.coverage (fun f : F => f.val) hOld
    q.cap q.repetitions q.length q.floor q.gain q.exceptions q.short q.smooth_length
    q.smooth_error q.list q.rate
  let f := fun j => s.signedFactorAt (s.selectedIndex q.cap σ π j)
  let G := F∪Finset.univ.image f
  refine ⟨G,Finset.subset_union_left,?_,?_⟩
  · apply Finset.union_subset Finset.subset_union_left
    intro g hg
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hg
    exact Finset.mem_union_right F (s.signed_mem_available _)
  · rw [q.schedule]
    unfold TimeLaw.info
    rw [FinLaw.cIf_finset_union]
    exact hh

theorem greedy_finite_selection (A : ℕ → Finset GaussianInt)
    (hA : ∀ j, A j⊆A (j+1)) (n : ℕ)
    (R : ℕ → Finset GaussianInt → Finset GaussianInt → Prop)
    (hstep : ∀ j≤n, ∀ F⊆A j, ∃ G, F⊆G ∧ G⊆A (j+1) ∧ R j F G) :
    ∃ F : ℕ → Finset GaussianInt,
      (∀ j, F j⊆A j) ∧ (∀ j, F j⊆F (j+1)) ∧ (∀ j≤n, R j (F j) (F (j+1))) := by
  have step (j : ℕ) (F : {F : Finset GaussianInt // F⊆A j}) :
      ∃ G : {G : Finset GaussianInt // G⊆A (j+1)}, F.val⊆G.val ∧ (j≤n → R j F.val G.val) := by
    by_cases hj : j≤n
    · obtain ⟨G,hFG,hG,hR⟩ := hstep j hj F.val F.property
      exact ⟨⟨G,hG⟩,hFG,fun _ => hR⟩
    · exact ⟨⟨F.val,F.property.trans (hA j)⟩,Finset.Subset.refl _,fun h => (hj h).elim⟩
  let f (j : ℕ) (F : {F : Finset GaussianInt // F⊆A j}) := (step j F).choose
  let F : (j : ℕ) → {F : Finset GaussianInt // F⊆A j} :=
    @Nat.rec (fun j => {F : Finset GaussianInt // F⊆A j}) ⟨∅,Finset.empty_subset _⟩ f
  refine ⟨fun j => (F j).val,fun j => (F j).property,?_,?_⟩
  · intro j
    exact (step j (F j)).choose_spec.1
  · intro j hj
    exact (step j (F j)).choose_spec.2 hj

noncomputable def precedingFactors (s : ℕ → SplitSieve) (j : ℕ) : Finset GaussianInt :=
  (Finset.range j).biUnion (fun i => (s i).availableFactors)

lemma precedingFactors_mono (s : ℕ → SplitSieve) {i j : ℕ} (h : i≤j) :
    precedingFactors s i⊆precedingFactors s j :=
by
  intro f hf
  obtain ⟨k,hk,hf⟩ := Finset.mem_biUnion.mp hf
  exact Finset.mem_biUnion.mpr ⟨k,(Finset.range_mono h) hk,hf⟩

lemma precedingFactors_succ (s : ℕ → SplitSieve) (j : ℕ) :
    precedingFactors s (j+1)=precedingFactors s j∪(s j).availableFactors := by
  simp only [precedingFactors,Finset.range_add_one,Finset.biUnion_insert,Finset.union_comm]

lemma precedingFactors_ne_zero (s : ℕ → SplitSieve) {j : ℕ} {f : GaussianInt}
    (h : f∈precedingFactors s j) : f≠0 := by
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp h
  exact (s i).available_ne_zero hi

theorem certificate_no_walk {D ε : ℝ} (hD : 1≤D) (ns : List ℕ) (N n : ℕ)
    (s : ℕ → SplitSieve) (L : ℕ → ℕ) (r : ℕ → ℝ)
    (cert : ∀ j≤n, BatchCertificate D ns N (s j) (L j)
      (residueWeight (precedingFactors s j)) (r j))
    (hdiv : ∀ j<n, L j∣L (j+1)) (hε : 0≤ε)
    (herr : ∀ j<n, ∀ a<L (j+1), 2*Real.binEntropy ((a:ℝ)/(N+1))+
      ((a:ℝ)/(N+1))*((L j:ℝ)*Real.log (latticeBall D).card+
        2*residueWeight (precedingFactors s (n+1)))≤ε)
    (hexcess : Real.log (latticeBall D).card+n*ε<∑ j∈Finset.range (n+1), r j)
    (z : ℕ → GaussianInt) (hz : Function.Injective z)
    (ha : ∀ j≤n, ∀ t, z t∈(s j).avoiding)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) : False := by
  let P := (TimeLaw.at 0).advance (commonSchedule z ns N)
  let rate (j : ℕ) (F G : Finset GaussianInt) := P.info
    (fun a (f : G) => residueCode f.val (z a)) (incrementWord z (L j))
    (fun a (f : F) => residueCode f.val (z a)) / L j
  obtain ⟨F,hFA,hFF,hR⟩ := greedy_finite_selection (precedingFactors s)
    (fun j => precedingFactors_mono s (Nat.le_succ j)) n
    (fun j F G => r j≤rate j F G) (by
      intro j hj F hF
      obtain ⟨G,hFG,hG,hI⟩ := (cert j hj).sound hD z hz (ha j hj) hs F
        (fun f hf => precedingFactors_ne_zero s (hF hf)) (residueWeight_mono hF)
      refine ⟨G,hFG,?_,hI⟩
      rw [precedingFactors_succ]
      exact hG.trans (Finset.union_subset_union_left hF))
  have ht := schedule_information_telescope z hs ns N n F hFF
    (fun j f hf => precedingFactors_ne_zero s (hFA j hf)) L
    (fun j hj => (cert j hj).length) hdiv (fun j hj => (cert j hj).smooth_length) hε (by
      intro j hj a ha
      have hw := residueWeight_mono ((hFA (j+1)).trans (precedingFactors_mono s (j := n+1) (by omega)))
      have hh := herr j hj a ha
      have hx : 0≤(a:ℝ)/(N+1) := by positivity
      change _+_ * (_+2*residueWeight (F (j+1)))≤ε
      nlinarith only [hw,hh,hx])
  have hh := Finset.sum_le_sum (s := Finset.range (n+1)) (fun j hj => hR j (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj))
  exact (not_lt_of_ge (hh.trans ht)) hexcess

open scoped BigOperators Classical
open Filter

theorem thin_bins (J : Finset ℕ) {K : ℕ} (hK : 0<K) :
    ∃ a<K, ((J.card:ℝ)/K)≤(J.filter (fun j => j%K=a)).card ∧
      ∀ i∈J.filter (fun j => j%K=a), ∀ j∈J.filter (fun j => j%K=a),
        i<j → i+K≤j := by
  have hh : (Finset.range K).card • ((J.card:ℝ)/K)≤(J.card:ℝ) := by
    rw [Finset.card_range,nsmul_eq_mul,mul_div_cancel₀ _ (by exact_mod_cast hK.ne')]
  obtain ⟨a,ha,hc⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := J) (t := Finset.range K) (f := fun j => j%K)
    (fun j _ => Finset.mem_range.mpr (Nat.mod_lt _ hK))
    (Finset.nonempty_range_iff.mpr hK.ne') hh
  refine ⟨a,Finset.mem_range.mp ha,hc,?_⟩
  intro i hi j hj hij
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  have hd : i%K=j%K := hi'.trans hj'.symm
  have hei := Nat.mod_add_div i K
  have hej := Nat.mod_add_div j K
  have hq : i/K<j/K := by nlinarith only [hei,hej,hd,hij]
  nlinarith only [hei,hej,hd,hq]

theorem eventually_separated_split_bins (K : ℕ) (hK : 0<K) :
    ∃ c δ : ℝ, 0<c ∧ 0<δ ∧ ∀ᶠ X : ℝ in atTop, ∃ J : Finset ℕ,
      c*X≤J.card ∧
      (∀ i∈J, ∀ j∈J, i<j → i+K≤j) ∧
      ∀ j∈J, X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*X ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(PrimeLogMass.dyadicBatch j).card := by
  obtain ⟨c,δ,hc,hδ,he⟩ := PrimeLogMass.eventually_dense_split_bins
  refine ⟨c/K,δ,div_pos hc (by exact_mod_cast hK),hδ,?_⟩
  filter_upwards [he] with X hX
  obtain ⟨J,hJ,hp⟩ := hX
  obtain ⟨a,_,hcard,hsep⟩ := thin_bins J hK
  refine ⟨J.filter (fun j => j%K=a),?_,hsep,?_⟩
  · have hh := (div_le_div_of_nonneg_right hJ (Nat.cast_nonneg K)).trans hcard
    simpa only [div_mul_eq_mul_div] using hh
  · intro j hj
    exact hp j (Finset.mem_filter.mp hj).1

lemma dyadicSieve_available_weight (j : ℕ) :
    residueWeight (dyadicSieve j).availableFactors≤4*Real.log 4*(2:ℝ)^j := by
  have hp : (∑ p∈PrimeLogMass.dyadicBatch j, Real.log (p:ℝ))≤Real.log 4*(2:ℝ)^(j+1) :=
    PrimeLogMass.prime_log_mass_le_theta _ (by positivity) (by
      intro p hp
      have h := (PrimeLogMass.mem_dyadicBatch j p).mp hp
      exact ⟨h.2.2.1,by exact_mod_cast h.2.1.le⟩)
  have hh := (dyadicSieve j).available_weight
  change residueWeight (dyadicSieve j).availableFactors≤2*∑ p∈PrimeLogMass.dyadicBatch j, Real.log (p:ℝ) at hh
  rw [pow_succ] at hp
  linarith only [hh,hp]

end

open scoped BigOperators Classical

lemma bandScale_add (g U : ℝ) (j k : ℕ) :
    bandScale g U (j+k)=bandScale g (bandScale g U j) k := by
  unfold bandScale
  rw [pow_add]
  ring

lemma bandLength_add (g U : ℝ) (j k : ℕ) :
    bandLength g U (j+k)=bandLength g (bandScale g U j) k := by
  unfold bandLength
  rw [bandScale_add]

lemma bandList_split (g U : ℝ) (j l r : ℕ) :
    List.ofFn (fun i : Fin (j+l+r) => bandLength g U i.val)=
      List.ofFn (fun i : Fin j => bandLength g U i.val)++
      List.ofFn (fun i : Fin l => bandLength g (bandScale g U j) i.val)++
      List.ofFn (fun i : Fin r => bandLength g (bandScale g U (j+l)) i.val) := by
  rw [List.ofFn_add,List.ofFn_add]
  simp only [Fin.val_castLE,Fin.val_natAdd,bandLength_add]

theorem band_first_crossing {g U V : ℝ} {m : ℕ} (hg : 0<g) (hg1 : g<1)
    (hV : 0<V) (hstart : V≤U) (hend : bandScale g U m≤V) :
    ∃ k, k ≤ m ∧ g^2*V<bandScale g U k ∧ bandScale g U k≤V := by
  have hex : ∃ k, bandScale g U k≤V := ⟨m,hend⟩
  let k := Nat.find hex
  have hk : bandScale g U k≤V := Nat.find_spec hex
  have hkm : k ≤ m := Nat.find_min' hex hend
  refine ⟨k,hkm,?_,hk⟩
  by_cases hk0 : k=0
  · simp only [hk0,bandScale,pow_zero,one_mul]
    have hg2 : g^2<1 := pow_lt_one₀ hg.le hg1 (by omega : 2≠0)
    exact (mul_lt_of_lt_one_left hV hg2).trans_le hstart
  · have hkpos : 0<k := Nat.pos_of_ne_zero hk0
    have hprev : V<bandScale g U (k-1) := lt_of_not_ge (Nat.find_min hex (by omega))
    have he : k=k-1+1 := by omega
    rw [he,bandScale_succ]
    exact mul_lt_mul_of_pos_left hprev (sq_pos_of_pos hg)

lemma bandScale_log {g U : ℝ} (hg : 0<g) (hU : 0<U) (k : ℕ) :
    Real.log (bandScale g U k)=(k:ℝ)*(2*Real.log g)+Real.log U := by
  unfold bandScale
  rw [Real.log_mul (ne_of_gt (pow_pos (sq_pos_of_pos hg) _)) hU.ne',Real.log_pow,Real.log_pow]
  norm_num

theorem schedule_log_bound (ns : List ℕ) (N : ℕ) {H : ℝ} (hH : 0≤H)
    (hns : ∀ n∈ns, (n:ℝ)≤Real.exp H) :
    Real.log ((ns.sum+N:ℕ)+1)≤Real.log ((ns.length:ℝ)+1)+H+Real.log ((N:ℝ)+1) := by
  have hs : (ns.sum:ℝ)≤(ns.length:ℝ)*Real.exp H := by
    induction ns with
    | nil => simp
    | cons n ns ih =>
      have hn := hns n (List.mem_cons_self ..)
      have hi := ih (fun m hm => hns m (List.mem_cons_of_mem n hm))
      simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      linarith only [hn,hi]
  have he : 1≤Real.exp H := Real.one_le_exp_iff.mpr hH
  have hc : 0≤(ns.length:ℝ)*Real.exp H := mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hN : 1≤(N:ℝ)+1 := by linarith only [(Nat.cast_nonneg N : (0:ℝ)≤N)]
  have hle : ((ns.sum+N:ℕ)+1:ℝ)≤((ns.length:ℝ)+1)*Real.exp H*((N:ℝ)+1) := by
    simp only [Nat.cast_add]
    nlinarith only [hs,he,hc,hN,(Nat.cast_nonneg N : (0:ℝ)≤N)]
  have hh := Real.log_le_log (show (0:ℝ)<((ns.sum+N:ℕ)+1) by positivity) hle
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_exp] at hh
  exact hh

end GaussianMoat

end OAI
end
end

section
section
namespace OAI

namespace GaussianMoat
open scoped BigOperators Classical

structure SieveCertificate (D : ℝ) where
  schedule : List ℕ
  smoothing : ℕ
  batches : ℕ → ℕ
  last : ℕ
  lengths : ℕ → ℕ
  rates : ℕ → ℝ
  error : ℝ
  batch : ∀ j≤last, BatchCertificate D schedule smoothing (dyadicSieve (batches j)) (lengths j)
    (residueWeight (precedingFactors (fun i => dyadicSieve (batches i)) j)) (rates j)
  divides : ∀ j<last, lengths j∣lengths (j+1)
  nonneg : 0≤error
  smooth : ∀ j<last, ∀ a<lengths (j+1), 2*Real.binEntropy ((a:ℝ)/(smoothing+1))+
    ((a:ℝ)/(smoothing+1))*((lengths j:ℝ)*Real.log (latticeBall D).card+
      2*residueWeight (precedingFactors (fun i => dyadicSieve (batches i)) (last+1)))≤error
  excess : Real.log (latticeBall D).card+last*error<∑ j∈Finset.range (last+1), rates j

noncomputable def SieveCertificate.primes {D : ℝ} (q : SieveCertificate D) : Finset ℕ :=
  (Finset.range (q.last+1)).biUnion (fun j => PrimeLogMass.dyadicBatch (q.batches j))

lemma SieveCertificate.primes_spec {D : ℝ} (q : SieveCertificate D) :
    ∀ p∈q.primes, p.Prime ∧ p%4=1 := by
  intro p hp
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hp
  exact (PrimeLogMass.mem_dyadicBatch _ _ |>.mp hj).2.2

noncomputable def SieveCertificate.sieve {D : ℝ} (q : SieveCertificate D) : SplitSieve :=
  splitSieveOf q.primes q.primes_spec

lemma SieveCertificate.avoiding_batch {D : ℝ} (q : SieveCertificate D)
    {z : GaussianInt} (hz : z∈q.sieve.avoiding) {j : ℕ} (hj : j≤q.last) :
    z∈(dyadicSieve (q.batches j)).avoiding := by
  intro p hp
  exact hz p (Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr (by omega),hp⟩)

theorem SieveCertificate.sound {D : ℝ} (q : SieveCertificate D) (hD : 1≤D) :
    ∀ z : ℕ → GaussianInt, (∀ t, z t∈q.sieve.avoiding) → Function.Injective z →
      (∀ t, dist (z (t+1):ℂ) (z t:ℂ)≤D) → False := by
  intro z ha hz hs
  exact certificate_no_walk hD q.schedule q.smoothing q.last
    (fun j => dyadicSieve (q.batches j)) q.lengths q.rates q.batch q.divides
    q.nonneg q.smooth q.excess z hz (fun _ hj t => q.avoiding_batch (ha t) hj)
    (fun t => by simpa only [dist_comm] using hs t)

theorem finiteSieve_of_certificates
    (h : ∀ D : ℝ, 1≤D → Nonempty (SieveCertificate D)) : FiniteSieveEndpoint := by
  intro D hD
  obtain ⟨q⟩ := h D hD
  exact ⟨q.sieve,q.sound hD⟩

theorem entropyBand_from_suffix (s : SplitSieve) (pre post : List ℕ) (N l : ℕ)
    {D g U δ : ℝ} (hD : 1≤D) (hg : 0<g) (hg1 : g≤1/200) (hU : 0<U)
    (hL : 1≤ s.meanLog)
    (hlog : 2*(1+Real.log 18)≤g*bandScale g U l)
    (hlarge : 640*s.meanLog≤g^5*bandScale g U l)
    (hsize : Real.log 16+Real.log (max D ((latticeBall (4*D)).card:ℝ))≤g^2*bandScale g U l)
    (hdisp : 4*Real.log D+2*Real.log 36≤4*g*bandScale g U l)
    (hgeom : 2*Real.log 16+4*Real.log D≤bandScale g U l/4)
    (hcap : ⌊U/s.meanLog⌋₊≤ s.primes.card)
    (hpost : ∀ n∈post, (n:ℝ)≤Real.exp (g*bandScale g U l))
    (hN : (N:ℝ)≤Real.exp (g*bandScale g U l))
    (hlen : (post.length+2:ℝ)≤Real.exp (g*bandScale g U l))
    (hconst : Real.log 36+2*Real.log D≤g*bandScale g U l)
    (hδ : (1/2:ℝ)^l+90*g≤δ) :
    Nonempty (EntropyBand s D
      (pre++List.ofFn (fun i : Fin l => bandLength g U i.val)++post)
      N (bandSize s g U l) δ) := by
  let V := bandScale g U l
  have hV : 0<V := bandScale_pos hg hU l
  have hLp : 0<s.meanLog := by linarith only [hL]
  have hg5 : g^5≤1 := pow_le_one₀ hg.le (by linarith only [hg1])
  have hVL : 2*s.meanLog≤V := by
    have hh := mul_le_mul_of_nonneg_right hg5 hV.le
    change 640*s.meanLog≤g^5*V at hlarge
    linarith only [hlarge,hh,hLp]
  have hfloor : V/2≤(bandSize s g U l:ℝ)*s.meanLog := by
    have hh := Nat.lt_floor_add_one (V/s.meanLog)
    have hm := mul_lt_mul_of_pos_right hh hLp
    rw [div_mul_cancel₀ _ hLp.ne',add_mul,one_mul] at hm
    change V/2≤(⌊V/s.meanLog⌋₊:ℝ)*s.meanLog
    linarith only [hm,hVL]
  have hshift := commonSchedule_log_bound (fun _ => (0:GaussianInt)) post N hpost hN hlen
  simp only [commonSchedule_bound,Nat.cast_add] at hshift
  rw [show 1+((post.sum:ℝ)+N)=(post.sum:ℝ)+N+1 by ring] at hshift
  have hcost : Real.log 36+2*Real.log (D*((post.sum+N:ℕ)+1))≤
      (10*g)*(bandSize s g U l:ℝ)*s.meanLog := by
    rw [Real.log_mul (by linarith only [hD] : D≠0) (by positivity)]
    simp only [Nat.cast_add]
    have hc : Real.log 36+2*Real.log D≤g*V := hconst
    have hm := mul_le_mul_of_nonneg_left hfloor (show 0≤10*g by positivity)
    linarith only [hshift,hc,hm]
  exact ⟨⟨pre,post,g,U,l,10*g,rfl,rfl,hg,hg1,hU,hlog,hlarge,hsize,hdisp,hgeom,
    hcap,hcost,by linarith only [hδ]⟩⟩

lemma bandLength_le_exp_start {g U : ℝ} (hg : 0≤g) (hg1 : g≤1) (hU : 0≤U) (j : ℕ) :
    (bandLength g U j:ℝ)≤Real.exp (g*U) := by
  apply (Nat.floor_le (Real.exp_nonneg _)).trans
  apply Real.exp_le_exp.mpr
  have hh := bandScale_antitone hg hg1 hU (Nat.zero_le j)
  simpa only [bandScale,pow_zero,one_mul] using mul_le_mul_of_nonneg_left hh hg

lemma bandLength_le_exp_at {g U : ℝ} (hg : 0≤g) (hg1 : g≤1) (hU : 0≤U)
    {i j : ℕ} (hij : i≤j) :
    (bandLength g U j:ℝ)≤Real.exp (g*bandScale g U i) := by
  exact (Nat.floor_le (Real.exp_nonneg _)).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (bandScale_antitone hg hg1 hU hij) hg))

end GaussianMoat

end OAI
end
end

section
section
namespace OAI

namespace GaussianMoat

section
open scoped BigOperators Classical

noncomputable def bandConstant (D : ℝ) : ℝ :=
  10000+100*|Real.log D|+100*|Real.log (max D ((latticeBall (4*D)).card:ℝ))|

lemma bandConstant_pos (D : ℝ) : 0<bandConstant D := by
  unfold bandConstant
  positivity

theorem entropyBand_from_margin (s : SplitSieve) (pre post : List ℕ) (N l : ℕ)
    {D g U δ : ℝ} (hD : 1≤D) (hg : 0<g) (hg1 : g≤1/200) (hU : 0<U)
    (hL : 1≤ s.meanLog)
    (hmargin : bandConstant D*s.meanLog≤g^5*bandScale g U l)
    (hcap : ⌊U/s.meanLog⌋₊≤ s.primes.card)
    (hpost : ∀ n∈post, (n:ℝ)≤Real.exp (g*bandScale g U l))
    (hN : (N:ℝ)≤Real.exp (g*bandScale g U l))
    (hlen : (post.length+2:ℝ)≤Real.exp (g*bandScale g U l))
    (hδ : (1/2:ℝ)^l+90*g≤δ) :
    Nonempty (EntropyBand s D
      (pre++List.ofFn (fun i : Fin l => bandLength g U i.val)++post)
      N (bandSize s g U l) δ) := by
  let V := bandScale g U l
  have hV : 0<V := bandScale_pos hg hU l
  have hg01 : g≤1 := by linarith only [hg1]
  have hg5 : g^5≤g := by
    have hh : g^4≤1 := pow_le_one₀ hg.le hg01
    calc g^5=g^4*g := by ring
         _ ≤ 1*g := mul_le_mul_of_nonneg_right hh hg.le
         _ = g := one_mul _
  have hg52 : g^5≤g^2 := by
    have hh : g^3≤1 := pow_le_one₀ hg.le hg01
    calc g^5=g^3*g^2 := by ring
         _ ≤ 1*g^2 := mul_le_mul_of_nonneg_right hh (sq_nonneg _)
         _ = g^2 := one_mul _
  have hC : bandConstant D≤g^5*V := by
    have hh := mul_le_mul_of_nonneg_left hL (bandConstant_pos D).le
    simp only [mul_one] at hh
    exact hh.trans hmargin
  have hCg := hC.trans (mul_le_mul_of_nonneg_right hg5 hV.le)
  have hCg2 := hC.trans (mul_le_mul_of_nonneg_right hg52 hV.le)
  have hCV := hCg.trans (by nlinarith only [hg01,hV] : g*V≤V)
  have hl16 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<16)
  have hl18 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<18)
  have hl36 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<36)
  have hld := le_abs_self (Real.log D)
  have hla := le_abs_self (Real.log (max D ((latticeBall (4*D)).card:ℝ)))
  have ha := abs_nonneg (Real.log D)
  have hb := abs_nonneg (Real.log (max D ((latticeBall (4*D)).card:ℝ)))
  have hC640 : 640≤bandConstant D := by unfold bandConstant; linarith only [ha,hb]
  apply entropyBand_from_suffix s pre post N l hD hg hg1 hU hL
  · dsimp only [bandConstant] at hCg
    linarith only [hCg,hl18,ha,hb]
  · exact (mul_le_mul_of_nonneg_right hC640 (by linarith only [hL])).trans hmargin
  · dsimp only [bandConstant] at hCg2
    linarith only [hCg2,hl16,hla,ha,hb]
  · dsimp only [bandConstant] at hCg
    linarith only [hCg,hl36,hld,ha,hb]
  · dsimp only [bandConstant] at hCV
    linarith only [hCV,hl16,hld,ha,hb]
  · exact hcap
  · exact hpost
  · exact hN
  · exact hlen
  · dsimp only [bandConstant] at hCg
    linarith only [hCg,hl36,hld,ha,hb]
  · exact hδ

open scoped BigOperators Classical
open Filter

theorem eventually_poly_le_exp (C : ℝ) {a : ℝ} (ha : 0<a) (d : ℕ) :
    ∀ᶠ y : ℝ in atTop, C*y^d≤a*Real.exp y := by
  by_cases hC : 0<C
  · have hh := (Real.isLittleO_pow_exp_atTop (n := d)).bound (div_pos ha hC)
    filter_upwards [hh,eventually_ge_atTop (0:ℝ)] with y hy hy0
    rw [Real.norm_of_nonneg (pow_nonneg hy0 _),Real.norm_of_nonneg (Real.exp_nonneg _)] at hy
    have hm := mul_le_mul_of_nonneg_left hy hC.le
    rwa [←mul_assoc,mul_div_cancel₀ _ hC.ne'] at hm
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
    exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hC) (pow_nonneg hy _)).trans
      (mul_nonneg ha.le (Real.exp_nonneg _))

theorem eventually_linear_le_square (A B : ℝ) :
    ∀ᶠ y : ℝ in atTop, A*y+B≤y^2 := by
  filter_upwards [eventually_ge_atTop (max (|A|+|B|+1) 1)] with y hy
  have h1 : 1≤y := (le_max_right _ _).trans hy
  have h2 : |A|+|B|+1≤y := (le_max_left _ _).trans hy
  have h3 : A≤|A| := le_abs_self _
  have h4 : B≤|B| := le_abs_self _
  nlinarith only [h1,h2,h3,h4,abs_nonneg A,abs_nonneg B]

noncomputable def accurateGrid (m : ℕ) : ℝ := Real.exp (-((m:ℝ)^2))
def accurateIterations (m : ℕ) : ℕ := 4*m^2

lemma accurateGrid_pos (m : ℕ) : 0<accurateGrid m := Real.exp_pos _

lemma accurateGrid_le_one (m : ℕ) : accurateGrid m≤1 := by
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))

lemma accurateIterations_error (m : ℕ) :
    (1/2:ℝ)^(accurateIterations m)+90*accurateGrid m≤91*accurateGrid m := by
  have hl : (1/2:ℝ)≤Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  have he : (1/2:ℝ)^(accurateIterations m)≤accurateGrid m := by
    rw [show (1/2:ℝ)=Real.exp (-Real.log 2) by rw [Real.exp_neg,Real.exp_log (by norm_num)]; norm_num]
    rw [←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    simp only [accurateIterations,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    nlinarith only [sq_nonneg (m:ℝ),hl]
  linarith only [he]

lemma accurateGrid_scale (m : ℕ) (a : ℝ) :
    bandScale (accurateGrid m) (Real.exp (a*Real.exp m)) (accurateIterations m)=
      Real.exp (a*Real.exp m-8*(m:ℝ)^4) := by
  unfold bandScale accurateGrid accurateIterations
  rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]
  congr 1
  push_cast
  ring

theorem eventually_accurate_scale {a : ℝ} (ha : 0<a) (k : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      Real.exp ((a/2)*Real.exp m)≤(accurateGrid m)^k *
        bandScale (accurateGrid m) (Real.exp (a*Real.exp m)) (accurateIterations m) := by
  have h4 := eventually_poly_le_exp 8 (a := a/4) (by positivity) 4
  have h2 := eventually_poly_le_exp (k:ℝ) (a := a/4) (by positivity) 2
  have hh := (h4.and h2).filter_mono (show Filter.map ((↑) : ℕ → ℝ) atTop≤atTop from tendsto_natCast_atTop_atTop)
  change ∀ᶠ m : ℕ in atTop, _ at hh
  filter_upwards [hh] with m hm
  rw [accurateGrid_scale]
  unfold accurateGrid
  rw [←Real.exp_nat_mul,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith only [hm.1,hm.2]

theorem eventually_accurate_error (C : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ m : ℕ in atTop, 91*accurateGrid m*(C*Real.exp m)≤ε := by
  by_cases hC : 0<C
  · have hh := eventually_linear_le_square 1 (Real.log (91*C/ε))
    have hh' := hh.filter_mono (show Filter.map ((↑) : ℕ → ℝ) atTop≤atTop from tendsto_natCast_atTop_atTop)
    filter_upwards [hh'] with m hm
    change 1*(m:ℝ)+Real.log (91*C/ε)≤(m:ℝ)^2 at hm
    have he : Real.exp ((m:ℝ)-(m:ℝ)^2)≤ε/(91*C) := by
      rw [←Real.exp_log (show 0<ε/(91*C) by positivity)]
      apply Real.exp_le_exp.mpr
      rw [Real.log_div (by positivity) (by positivity)]
      rw [Real.log_div (by positivity) hε.ne'] at hm
      linarith only [hm]
    have hmul := (le_div_iff₀ (show 0<91*C by positivity)).mp he
    unfold accurateGrid
    rw [show 91*Real.exp (-((m:ℝ)^2))*(C*Real.exp m)=
      Real.exp ((m:ℝ)-(m:ℝ)^2)*(91*C) by rw [Real.exp_sub,Real.exp_neg]; ring]
    exact hmul
  · filter_upwards [] with m
    have : C*Real.exp (m:ℝ)≤0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hC) (Real.exp_nonneg _)
    exact (mul_nonpos_of_nonneg_of_nonpos (by exact mul_nonneg (by norm_num) (accurateGrid_pos m).le : 0≤91*accurateGrid m) this).trans hε.le

end

section
open scoped BigOperators Classical
open Filter

lemma eventually_const_le_exp_mul {a : ℝ} (ha : 0<a) (C : ℝ) :
    ∀ᶠ m : ℕ in atTop, C≤a*Real.exp m := by
  have hh : Tendsto (fun m : ℕ => Real.exp (m:ℝ)*a) atTop atTop :=
    (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop).atTop_mul_const ha
  simpa only [mul_comm] using hh.eventually (eventually_ge_atTop C)

lemma eventually_mul_le_double_exp {a : ℝ} (ha : 0<a) (C : ℝ) :
    ∀ᶠ m : ℕ in atTop, C*Real.exp m≤Real.exp (a*Real.exp m) := by
  have hh := eventually_poly_le_exp (C/a) (a := 1) (by norm_num) 1
  have ht : Tendsto (fun m : ℕ => a*Real.exp m) atTop atTop := by
    simpa only [Function.comp_apply] using Filter.Tendsto.const_mul_atTop ha
      (Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [ht.eventually hh] with m hm
  simpa only [pow_one,one_mul,←mul_assoc,div_mul_cancel₀ _ ha.ne'] using hm

lemma eventually_accurate_small {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ m : ℕ in atTop, accurateGrid m≤ε := by
  have hh := eventually_linear_le_square 0 (-Real.log ε)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hh] with m hm
  change 0*(m:ℝ)-Real.log ε≤(m:ℝ)^2 at hm
  unfold accurateGrid
  rw [←Real.exp_log hε]
  apply Real.exp_le_exp.mpr
  linarith only [hm]

lemma dense_sieve_cap (s : SplitSieve) (hne : s.primes.Nonempty) {T δ U : ℝ}
    (hT : 2≤T)
    (hp : ∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T)
    (hdense : δ*T/Real.log (2*T)≤ s.primes.card)
    (hsize : 2*U≤δ*T) : ⌊U/s.meanLog⌋₊≤ s.primes.card := by
  have hT0 : 0<T := by linarith only [hT]
  have hlogT : 0<Real.log T := Real.log_pos (by linarith only [hT])
  have hm := s.meanLog_bounds hne hT0 hp
  have hmean : 0<s.meanLog := hlogT.trans_le hm.1
  have hl2 : Real.log 2≤Real.log T := Real.log_le_log (by norm_num) hT
  have hhlog : Real.log (2*T)≤2*s.meanLog := by
    rw [Real.log_mul (by norm_num) hT0.ne']
    linarith only [hl2,hm.1]
  have hlo : 0<Real.log (2*T) := Real.log_pos (by linarith only [hT])
  have hd : δ*T≤(s.primes.card:ℝ)*Real.log (2*T) := (div_le_iff₀ hlo).mp hdense
  have hk : δ*T≤(s.primes.card:ℝ)*(2*s.meanLog) := hd.trans
    (mul_le_mul_of_nonneg_left hhlog (Nat.cast_nonneg _))
  apply Nat.floor_le_of_le
  apply (div_le_iff₀ hmean).mpr
  linarith only [hsize,hk]

theorem eventually_accurate_band {D A B a b δ : ℝ}
    (hD : 1≤D) (hA : 0<A) (ha : 0<a) (haA : a<A)
    (hba : b≤a/2) (hδ : 0<δ) :
    ∀ᶠ m : ℕ in atTop, ∀ (s : SplitSieve) (T : ℝ) (pre post : List ℕ) (N : ℕ),
      s.primes.Nonempty →
      (∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T) →
      δ*T/Real.log (2*T)≤ s.primes.card →
      Real.exp (A*Real.exp m)≤T → Real.log T≤B*Real.exp m →
      (∀ n∈post, (n:ℝ)≤Real.exp (Real.exp (b*Real.exp m))) →
      (N:ℝ)≤Real.exp (Real.exp (b*Real.exp m)) →
      (post.length+2:ℝ)≤Real.exp (Real.exp (b*Real.exp m)) →
      Nonempty (EntropyBand s D
        (pre++List.ofFn (fun i : Fin (accurateIterations m) =>
          bandLength (accurateGrid m) (Real.exp (a*Real.exp m)) i.val)++post)
        N (bandSize s (accurateGrid m) (Real.exp (a*Real.exp m)) (accurateIterations m))
        (91*accurateGrid m)) := by
  have hlarge := eventually_mul_le_double_exp (a := a/2) (by positivity)
    (bandConstant D*(B+1))
  have hgap := eventually_const_le_exp_mul (a := A-a) (by linarith only [haA]) (Real.log (2/δ))
  have htwo := eventually_const_le_exp_mul hA 2
  filter_upwards [eventually_accurate_scale ha 5,eventually_accurate_scale ha 1,
    eventually_accurate_small (show (0:ℝ)<1/200 by norm_num),hlarge,hgap,htwo]
    with m hm5 hm1 hsmall hlarge hgap htwo
  intro s T pre post N hne hp hdense hT hThi hpost hN hlen
  have he1 : 1≤Real.exp (m:ℝ) := Real.one_le_exp_iff.mpr (Nat.cast_nonneg _)
  have hT0 : 0<T := (Real.exp_pos _).trans_le hT
  have hT2 : 2≤T := by
    have hh := Real.add_one_le_exp (A*Real.exp m)
    linarith only [hh,htwo,hT]
  have hm := s.meanLog_bounds hne hT0 hp
  have hmean : 1≤ s.meanLog := by
    have hh := Real.log_le_log (Real.exp_pos _) hT
    rw [Real.log_exp] at hh
    linarith only [hh,hm.1,htwo]
  have hl2 : Real.log 2≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith only [hh]
  have hmean' : s.meanLog≤(B+1)*Real.exp m := by
    rw [Real.log_mul (by norm_num) hT0.ne'] at hm
    linarith only [hm.2,hThi,hl2,he1]
  have hmargin := (mul_le_mul_of_nonneg_left hmean' (bandConstant_pos D).le).trans
    (by simpa only [mul_assoc] using hlarge.trans hm5)
  have hsize : 2*Real.exp (a*Real.exp m)≤δ*T := by
    have he : Real.exp (a*Real.exp m+Real.log (2/δ))≤Real.exp (A*Real.exp m) := by
      apply Real.exp_le_exp.mpr
      linarith only [hgap]
    rw [Real.exp_add,Real.exp_log (div_pos (by norm_num) hδ)] at he
    have hh := mul_le_mul_of_nonneg_left (he.trans hT) hδ.le
    have heq : δ*(Real.exp (a*Real.exp m)*(2/δ))=2*Real.exp (a*Real.exp m) := by field_simp
    rwa [heq] at hh
  have hcap := dense_sieve_cap s hne hT2 hp hdense hsize
  have htail : Real.exp (b*Real.exp m)≤accurateGrid m*
      bandScale (accurateGrid m) (Real.exp (a*Real.exp m)) (accurateIterations m) := by
    simpa only [pow_one] using ((Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hba (Real.exp_nonneg _))).trans hm1)
  exact entropyBand_from_margin s pre post N (accurateIterations m) hD (accurateGrid_pos m)
    hsmall (Real.exp_pos _) hmean hmargin hcap
    (fun n hn => (hpost n hn).trans (Real.exp_le_exp.mpr htail))
    (hN.trans (Real.exp_le_exp.mpr htail)) (hlen.trans (Real.exp_le_exp.mpr htail))
    (accurateIterations_error m)

end

open scoped BigOperators Classical

lemma EntropyBand.size_cap {s : SplitSieve} {D δ : ℝ} {ns : List ℕ} {N b : ℕ}
    (q : EntropyBand s D ns N b δ) (hmean : 0< s.meanLog) : b≤ s.primes.card := by
  rw [q.size]
  apply le_trans _ q.cap
  apply Nat.floor_mono
  apply div_le_div_of_nonneg_right _ hmean.le
  have hh := bandScale_antitone q.positive.le (by linarith only [q.small]) q.scale.le (Nat.zero_le q.l)
  simpa only [bandScale,pow_zero,one_mul] using hh

lemma EntropyBand.size_lower {s : SplitSieve} {D δ : ℝ} {ns : List ℕ} {N b : ℕ}
    (q : EntropyBand s D ns N b δ) (hmean : 0< s.meanLog) :
    bandScale q.g q.U q.l/2≤(b:ℝ)*s.meanLog := by
  have hV := bandScale_pos q.positive q.scale q.l
  have hg5 : q.g^5≤1 := pow_le_one₀ q.positive.le (by linarith only [q.small])
  have hh := mul_le_mul_of_nonneg_right hg5 hV.le
  have hlarge := q.large
  have hVL : 2*s.meanLog≤bandScale q.g q.U q.l := by linarith only [hh,hlarge,hmean]
  have hf := Nat.lt_floor_add_one (bandScale q.g q.U q.l/s.meanLog)
  have hm := mul_lt_mul_of_pos_right hf hmean
  rw [div_mul_cancel₀ _ hmean.ne',add_mul,one_mul] at hm
  have ht : bandScale q.g q.U q.l/2≤(⌊bandScale q.g q.U q.l/s.meanLog⌋₊:ℝ)*s.meanLog := by
    linarith only [hm,hVL]
  simpa only [q.size,bandSize] using ht

lemma EntropyBand.size_pos {s : SplitSieve} {D δ : ℝ} {ns : List ℕ} {N b : ℕ}
    (q : EntropyBand s D ns N b δ) (hmean : 0< s.meanLog) : 0<b := by
  have hh := q.size_lower hmean
  have hV := bandScale_pos q.positive q.scale q.l
  by_contra h
  have hb : b=0 := by omega
  have he : (b:ℝ)=0 := by exact_mod_cast hb
  rw [he,zero_mul] at hh
  linarith only [hh,hV]

lemma bandSize_lower_of_scale {s : SplitSieve} {g U C T : ℝ} {l : ℕ}
    (hmean : 0< s.meanLog) (hlog : 0<Real.log T)
    (hm : s.meanLog≤2*Real.log T)
    (hV : 2*s.meanLog≤bandScale g U l)
    (hscale : C*T≤bandScale g U l) :
    C*T/(4*Real.log T)≤(bandSize s g U l:ℝ) := by
  have hf := Nat.lt_floor_add_one (bandScale g U l/s.meanLog)
  have hh := mul_lt_mul_of_pos_right hf hmean
  rw [div_mul_cancel₀ _ hmean.ne',add_mul,one_mul] at hh
  have hlo : bandScale g U l/2≤(bandSize s g U l:ℝ)*s.meanLog := by
    change _≤(⌊bandScale g U l/s.meanLog⌋₊:ℝ)*_
    linarith only [hh,hV]
  have hu := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (bandSize s g U l))
  apply (div_le_iff₀ (by positivity)).mpr
  linarith only [hlo,hu,hscale]

end GaussianMoat

end OAI
end
end

section
section
namespace OAI


namespace GaussianMoat

section
open scoped BigOperators Classical
open Filter

noncomputable def topParameter : ℝ := 1/1000000
def topIterations : ℕ := 20
noncomputable def topCoefficient (a : ℝ) : ℝ := (topParameter^2)^topIterations*a

lemma topParameter_pos : 0<topParameter := by norm_num [topParameter]
lemma topParameter_small : topParameter≤1/200 := by norm_num [topParameter]
lemma topCoefficient_pos {a : ℝ} (ha : 0<a) : 0<topCoefficient a := by
  unfold topCoefficient; exact mul_pos (pow_pos (sq_pos_of_pos topParameter_pos) _) ha
lemma top_deficit : (1/2:ℝ)^topIterations+90*topParameter≤1/10000 := by
  norm_num [topParameter,topIterations]

theorem eventually_top_band {D a δ : ℝ} (hD : 1≤D) (ha : 0<a)
    (haδ : 2*a≤δ) :
    ∀ᶠ x : ℝ in atTop, ∀ (s : SplitSieve) (pre post : List ℕ),
      s.primes.Nonempty →
      (∀ p∈s.primes, Real.exp x≤(p:ℝ) ∧ (p:ℝ)≤2*Real.exp x) →
      δ*Real.exp x/Real.log (2*Real.exp x)≤ s.primes.card →
      (∀ n∈post, (n:ℝ)≤Real.exp (topParameter*topCoefficient a*Real.exp x)) →
      (post.length+2:ℝ)≤Real.exp (topParameter*topCoefficient a*Real.exp x) →
      Nonempty (EntropyBand s D
        (pre++List.ofFn (fun i : Fin topIterations =>
          bandLength topParameter (a*Real.exp x) i.val)++post)
        0 (bandSize s topParameter (a*Real.exp x) topIterations) (1/10000)) ∧
      topCoefficient a*Real.exp x/(4*x)≤
        (bandSize s topParameter (a*Real.exp x) topIterations:ℝ) := by
  have hc := topCoefficient_pos ha
  have hlarge := eventually_poly_le_exp (2*bandConstant D)
    (a := topParameter^5*topCoefficient a) (mul_pos (pow_pos topParameter_pos _) hc) 1
  filter_upwards [hlarge,eventually_ge_atTop (2:ℝ)] with x hlarge hx
  intro s pre post hne hp hdense hpost hlen
  have hT2 : 2≤Real.exp x := by linarith only [Real.add_one_le_exp x,hx]
  have hm := s.meanLog_bounds hne (Real.exp_pos x) hp
  rw [Real.log_exp] at hm
  have hmean : 1≤ s.meanLog := by linarith only [hm.1,hx]
  have hmean0 : 0< s.meanLog := by linarith only [hmean]
  have hlog2 : Real.log 2≤x := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith only [hh,hx]
  have hmean' : s.meanLog≤2*x := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp] at hm
    linarith only [hm.2,hlog2]
  have hscale : bandScale topParameter (a*Real.exp x) topIterations=topCoefficient a*Real.exp x := by
    unfold bandScale topCoefficient; ring
  have hmargin : bandConstant D*s.meanLog≤topParameter^5*
      bandScale topParameter (a*Real.exp x) topIterations := by
    have hh := mul_le_mul_of_nonneg_left hmean' (bandConstant_pos D).le
    rw [hscale]
    simp only [pow_one] at hlarge
    linarith only [hh,hlarge]
  have hcap := dense_sieve_cap s hne hT2 hp hdense
    (by nlinarith only [haδ,Real.exp_pos x] : 2*(a*Real.exp x)≤δ*Real.exp x)
  have hband := entropyBand_from_margin s pre post 0 topIterations hD topParameter_pos
    topParameter_small (mul_pos ha (Real.exp_pos _)) hmean hmargin hcap
    (by simpa only [hscale,mul_assoc] using hpost)
    (by simp only [Nat.cast_zero]; positivity)
    (by simpa only [hscale,mul_assoc] using hlen) top_deficit
  refine ⟨hband,?_⟩
  have hg5 : topParameter^5≤1 := pow_le_one₀ topParameter_pos.le (by norm_num [topParameter])
  have hVpos := bandScale_pos topParameter_pos (mul_pos ha (Real.exp_pos x)) topIterations
  have hn := mul_le_mul_of_nonneg_right hg5 hVpos.le
  have hC : 2≤bandConstant D := by
    unfold bandConstant
    linarith only [abs_nonneg (Real.log D),abs_nonneg (Real.log (max D ((latticeBall (4*D)).card:ℝ)))]
  have hm2 := mul_le_mul_of_nonneg_right hC hmean0.le
  have hV : 2*s.meanLog≤bandScale topParameter (a*Real.exp x) topIterations := by
    linarith only [hmargin,hn,hm2]
  have hh := bandSize_lower_of_scale hmean0
    (show 0<Real.log (Real.exp x) by rw [Real.log_exp]; linarith only [hx])
    (by simpa only [Real.log_exp] using hmean') hV (le_of_eq hscale.symm)
  simpa only [Real.log_exp] using hh

end

open scoped BigOperators Classical

noncomputable def topBlock (a : ℝ) (j : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin topIterations => bandLength topParameter (a*(2:ℝ)^j) i.val)

noncomputable def topBlocks (a : ℝ) (J : Finset ℕ) : List ℕ :=
  (J.sort (·≥·)).flatMap (topBlock a)

noncomputable def accurateBlock (m : ℕ) (a : ℝ) : List ℕ :=
  List.ofFn (fun i : Fin (accurateIterations m) =>
    bandLength (accurateGrid m) (Real.exp (a*Real.exp m)) i.val)

lemma topBlocks_length (a : ℝ) (J : Finset ℕ) :
    (topBlocks a J).length=J.card*topIterations := by
  unfold topBlocks
  rw [List.length_flatMap]
  simp only [topBlock,List.length_ofFn,List.map_const',List.sum_replicate,Finset.length_sort,
    smul_eq_mul]

lemma topBlock_bound {a H : ℝ} (ha : 0≤a) (j : ℕ)
    (h : topParameter*a*(2:ℝ)^j≤H) :
    ∀ n∈topBlock a j, (n:ℝ)≤Real.exp H := by
  intro n hn
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hn
  exact (bandLength_le_exp_start topParameter_pos.le
    (by norm_num [topParameter]) (mul_nonneg ha (by positivity)) i.val).trans
    (Real.exp_le_exp.mpr (by simpa only [mul_assoc] using h))

lemma accurateBlock_bound {a H : ℝ} {m : ℕ} (hg : accurateGrid m≤1)
    (h : accurateGrid m*Real.exp (a*Real.exp m)≤H) :
    ∀ n∈accurateBlock m a, (n:ℝ)≤Real.exp H := by
  intro n hn
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hn
  exact (bandLength_le_exp_start (accurateGrid_pos m).le hg (Real.exp_nonneg _) i.val).trans
    (Real.exp_le_exp.mpr h)

lemma sorted_split {J : Finset ℕ} {j : ℕ} (hj : j∈J) :
    ∃ pre post : List ℕ, J.sort (·≥·)=pre++j::post ∧
      (∀ i∈post, i∈J ∧ i < j) ∧ (∀ i∈pre, i∈J ∧ j < i) := by
  have hm : j∈J.sort (·≥·) := (Finset.mem_sort (·≥·)).mpr hj
  obtain ⟨pre,post,he⟩ := List.mem_iff_append.mp hm
  have hp : (J.sort (·≥·)).Pairwise (·>·) := by
    exact (Finset.sortedGT_sort J).pairwise
  rw [he,List.pairwise_append,List.pairwise_cons] at hp
  refine ⟨pre,post,he,?_,?_⟩
  · intro i hi
    refine ⟨(Finset.mem_sort (·≥·)).mp ?_,hp.2.1.1 i hi⟩
    rw [he]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hi)
  · intro i hi
    refine ⟨(Finset.mem_sort (·≥·)).mp ?_,hp.2.2 i hi j (List.mem_cons_self ..)⟩
    rw [he]; exact List.mem_append_left _ hi

lemma topBlocks_split {a : ℝ} {J : Finset ℕ} {j : ℕ} (hj : j∈J) :
    ∃ pre post : List ℕ, topBlocks a J=pre++topBlock a j++post ∧
      post.length≤J.card*topIterations ∧
      (∀ n∈post, ∃ i∈J, i<j ∧ n∈topBlock a i) := by
  obtain ⟨A,B,he,hB,_⟩ := sorted_split hj
  refine ⟨A.flatMap (topBlock a),B.flatMap (topBlock a),?_,?_,?_⟩
  · simp only [topBlocks,he,List.flatMap_append,List.flatMap_cons,List.append_assoc]
  · have hh : (B.flatMap (topBlock a)).length≤(topBlocks a J).length := by
      simp only [topBlocks,he,List.flatMap_append,List.flatMap_cons,List.length_append]
      omega
    simpa only [topBlocks_length] using hh
  · intro n hn
    obtain ⟨i,hi,hn⟩ := List.mem_flatMap.mp hn
    exact ⟨i,(hB i hi).1,(hB i hi).2,hn⟩

noncomputable def windowBlocks (a : ℝ) (m : ℕ) (J : ℕ → Finset ℕ) (W : ℕ) : List ℕ :=
  ((List.range W).reverse).flatMap (fun w =>
    topBlocks a (J w)++accurateBlock m ((100:ℝ)^w/4))

lemma windowBlocks_succ (a : ℝ) (m : ℕ) (J : ℕ → Finset ℕ) (W : ℕ) :
    windowBlocks a m J (W+1)=topBlocks a (J W)++accurateBlock m ((100:ℝ)^W/4)++
      windowBlocks a m J W := by
  simp only [windowBlocks,List.range_succ,List.reverse_append,List.reverse_singleton,
    List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]

lemma windowBlocks_split (a : ℝ) (m : ℕ) (J : ℕ → Finset ℕ) {W w : ℕ} (hw : w<W) :
    ∃ pre, windowBlocks a m J W=pre++topBlocks a (J w)++
      accurateBlock m ((100:ℝ)^w/4)++windowBlocks a m J w := by
  induction W with
  | zero => omega
  | succ W ih =>
    rw [windowBlocks_succ]
    by_cases he : w=W
    · subst w; exact ⟨[],by simp only [List.nil_append]⟩
    · obtain ⟨pre,hp⟩ := ih (by omega)
      rw [hp]
      exact ⟨topBlocks a (J W)++accurateBlock m ((100:ℝ)^W/4)++pre,by simp only [List.append_assoc]⟩

lemma windowBlocks_mem (a : ℝ) (m : ℕ) (J : ℕ → Finset ℕ) {W n : ℕ}
    (hn : n∈windowBlocks a m J W) :
    ∃ w<W, n∈topBlocks a (J w) ∨ n∈accurateBlock m ((100:ℝ)^w/4) := by
  obtain ⟨w,hw,hn⟩ := List.mem_flatMap.mp hn
  exact ⟨w,List.mem_range.mp (List.mem_reverse.mp hw),List.mem_append.mp hn⟩

theorem separated_power_sum (J : Finset ℕ) {K j : ℕ} (hK : 0<K)
    (hsep : ∀ a∈J, ∀ b∈J, a<b → a+K≤b)
    (hcap : ∀ a∈J, a+K≤j) :
    (∑ a∈J, (2:ℝ)^a)≤(2:ℝ)^j/((2:ℝ)^K-1) := by
  have hden : 0<(2:ℝ)^K-1 := by
    have hh := one_lt_pow₀ (by norm_num : (1:ℝ)<2) (by omega : K≠0)
    linarith only [hh]
  induction J using Finset.induction_on_max generalizing j with
  | empty => simp only [Finset.sum_empty]; positivity
  | @insert a J hmax ih =>
    have ha : a∉J := fun h => (lt_irrefl a) (hmax a h)
    have hci : ∀ b∈J, b+K≤a := by
      intro b hb
      exact hsep b (Finset.mem_insert_of_mem hb) a (Finset.mem_insert_self ..)
        (hmax b hb)
    have hi := ih (fun b hb c hc hbc => hsep b (Finset.mem_insert_of_mem hb)
      c (Finset.mem_insert_of_mem hc) hbc) hci
    rw [Finset.sum_insert ha]
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (hcap a (Finset.mem_insert_self ..))
    have hd := (div_le_div_iff_of_pos_right hden).mpr hp
    rw [pow_add] at hd
    have he : (2:ℝ)^a+(2:ℝ)^a/((2:ℝ)^K-1)=(2:ℝ)^a*2^K/(2^K-1) := by
      field_simp; ring
    exact (add_le_add (le_refl ((2:ℝ)^a)) hi).trans (he ▸ hd)

lemma residueWeight_union_le (F G : Finset GaussianInt) :
    residueWeight (F∪G)≤residueWeight F+residueWeight G := by
  classical
  have hh := Finset.sum_union_inter (s₁ := F) (s₂ := G) (f := fun f : GaussianInt => Real.log f.norm.natAbs)
  change residueWeight (F∪G)+residueWeight (F∩G)=residueWeight F+residueWeight G at hh
  linarith only [hh,residueWeight_nonneg (F∩G)]

lemma residueWeight_biUnion_le {ι : Type uIota} (J : Finset ι) (F : ι → Finset GaussianInt) :
    residueWeight (J.biUnion F)≤∑ j∈J, residueWeight (F j) := by
  induction J using Finset.induction_on with
  | empty => simp [residueWeight]
  | @insert j J hj ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert hj]
    exact (residueWeight_union_le _ _).trans (add_le_add (le_refl _) ih)

lemma separated_factor_cost (J : Finset ℕ) {K j : ℕ} (hK : 0<K)
    (hsep : ∀ a∈J, ∀ b∈J, a<b → a+K≤b)
    (hcap : ∀ a∈J, a+K≤j) :
    residueWeight (J.biUnion (fun a => (dyadicSieve a).availableFactors))≤
      (4*Real.log 4/((2:ℝ)^K-1))*(2:ℝ)^j := by
  have hsum := Finset.sum_le_sum (fun a (_ : a∈J) => dyadicSieve_available_weight a)
  rw [←Finset.mul_sum] at hsum
  have hh := mul_le_mul_of_nonneg_left (separated_power_sum J hK hsep hcap)
    (show 0≤4*Real.log 4 by positivity)
  have ht := (residueWeight_biUnion_le J (fun a => (dyadicSieve a).availableFactors)).trans (hsum.trans hh)
  calc
    _ ≤ 4*Real.log 4*((2:ℝ)^j/(2^K-1)) := ht
    _ = _ := by ring

open scoped BigOperators Classical
open Filter

lemma log_two_lower : (1/2:ℝ)≤Real.log 2 := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at hh
  exact hh

lemma narrow_bins_card {X : ℝ} (hX : 2≤X) (J : Finset ℕ)
    (hJ : ∀ j∈J, (j:ℝ)*Real.log 2≤21/20*X) :
    (J.card:ℝ)≤3*X := by
  have hj : ∀ j∈J, (j:ℝ)≤21/10*X := by
    intro j hj
    have hh := mul_le_mul_of_nonneg_left log_two_lower (Nat.cast_nonneg j)
    linarith only [hh,hJ j hj]
  have hs : J⊆Finset.range (⌊21/10*X⌋₊+1) := by
    intro j hj'
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le ((Nat.le_floor_iff (by positivity)).mpr (hj j hj'))
  have hc : (J.card:ℝ)≤(⌊21/10*X⌋₊:ℝ)+1 := by
    exact_mod_cast (Finset.card_le_card hs).trans_eq (Finset.card_range _)
  have hf := Nat.floor_le (show 0≤21/10*X by linarith only [hX])
  linarith only [hc,hf,hX]

lemma topBlock_separated {a : ℝ} (ha : 0<a) {i j K : ℕ}
    (hgap : a≤(2:ℝ)^K*topCoefficient a) (hij : i+K≤j) :
    ∀ n∈topBlock a i, (n:ℝ)≤Real.exp (topParameter*topCoefficient a*(2:ℝ)^j) := by
  apply topBlock_bound ha.le
  have hh := mul_le_mul_of_nonneg_left hgap (show 0≤(2:ℝ)^i by positivity)
  rw [←mul_assoc,←pow_add] at hh
  have hp : (2:ℝ)^(i+K)≤(2:ℝ)^j := pow_le_pow_right₀ (by norm_num) hij
  have hp' := mul_le_mul_of_nonneg_right hp (topCoefficient_pos ha).le
  have hg := mul_le_mul_of_nonneg_left (hh.trans hp') topParameter_pos.le
  linarith only [hg]

theorem eventually_window_top {D a δ : ℝ} {K : ℕ}
    (hD : 1≤D) (ha : 0<a) (haδ : 2*a≤δ)
    (hgap : a≤(2:ℝ)^K*topCoefficient a) :
    ∀ᶠ X : ℝ in atTop, ∀ (J : Finset ℕ) (initial : List ℕ),
      (∀ i∈J, ∀ j∈J, i<j → i+K≤j) →
      (∀ j∈J, X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*X ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(PrimeLogMass.dyadicBatch j).card) →
      ∀ j∈J, Nonempty (EntropyBand (dyadicSieve j) D (initial++topBlocks a J)
        0 (bandSize (dyadicSieve j) topParameter (a*(2:ℝ)^j) topIterations) (1/10000)) ∧
        topCoefficient a*(2:ℝ)^j/(4*Real.log ((2:ℝ)^j))≤
          (bandSize (dyadicSieve j) topParameter (a*(2:ℝ)^j) topIterations:ℝ) := by
  have hδ : 0<δ := by linarith only [ha,haδ]
  have htop := eventually_top_band hD ha haδ
  have hlen := eventually_poly_le_exp (100:ℝ)
    (a := topParameter*topCoefficient a) (mul_pos topParameter_pos (topCoefficient_pos ha)) 1
  obtain ⟨x0,h0⟩ := eventually_atTop.mp (htop.and hlen)
  filter_upwards [eventually_ge_atTop (max x0 2)] with X hX
  intro J initial hsep hJ j hj
  have hX2 : 2≤X := (le_max_right _ _).trans hX
  have hX0 : x0≤X := (le_max_left _ _).trans hX
  have hlog := (hJ j hj).1
  have hlog' := (hJ j hj).2.1
  obtain ⟨hband,hlen⟩ := h0 (j*Real.log 2) (hX0.trans hlog)
  have hn : (dyadicSieve j).primes.Nonempty := by
    apply Finset.card_pos.mp
    have hlogp : 0<Real.log ((2:ℝ)^(j+1)) := by
      rw [Real.log_pow]
      positivity
    have hh := (hJ j hj).2.2
    have hp : 0<δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1)) := div_pos (by positivity) hlogp
    have hc : (0:ℝ)<(PrimeLogMass.dyadicBatch j).card := hp.trans_le hh
    exact_mod_cast hc
  obtain ⟨pre,post,he,hpl,hpm⟩ := topBlocks_split (a := a) hj
  have hT : Real.exp (j*Real.log 2)=(2:ℝ)^j := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  have hcard := narrow_bins_card hX2 J (fun i hi => (hJ i hi).2.1)
  have hlen' : (post.length+2:ℝ)≤Real.exp (topParameter*topCoefficient a*(2:ℝ)^j) := by
    have hp : (post.length:ℝ)≤(J.card:ℝ)*topIterations := by exact_mod_cast hpl
    simp only [pow_one,hT] at hlen
    have he := Real.add_one_le_exp (topParameter*topCoefficient a*(2:ℝ)^j)
    norm_num only [topIterations,Nat.cast_ofNat] at hp
    linarith only [hp,hcard,hlen,he,hlog,hX2]
  have hprime : ∀ p∈(dyadicSieve j).primes, Real.exp (j*Real.log 2)≤(p:ℝ) ∧
      (p:ℝ)≤2*Real.exp (j*Real.log 2) := by
    intro p hp
    rw [hT]
    have hh := (PrimeLogMass.mem_dyadicBatch j p).mp hp
    constructor
    · exact_mod_cast hh.1
    · have hh' : p≤2^(j+1) := hh.2.1.le
      rw [pow_succ] at hh'
      exact_mod_cast (by simpa only [mul_comm] using hh' : p≤2*2^j)
  have hdense : δ*Real.exp (j*Real.log 2)/Real.log (2*Real.exp (j*Real.log 2))≤
      (dyadicSieve j).primes.card := by
    change δ*Real.exp (j*Real.log 2)/Real.log (2*Real.exp (j*Real.log 2))≤
      (PrimeLogMass.dyadicBatch j).card
    simpa only [hT,pow_succ,mul_comm] using (hJ j hj).2.2
  have hpst : ∀ n∈post, (n:ℝ)≤Real.exp (topParameter*topCoefficient a*Real.exp (j*Real.log 2)) := by
    intro n hnp
    obtain ⟨i,hi,hij,hni⟩ := hpm n hnp
    rw [hT]
    exact topBlock_separated ha hgap (hsep i hi j hj hij) n hni
  obtain ⟨hb,hbsize⟩ := hband (dyadicSieve j) (initial++pre) post hn hprime hdense hpst
    (by simpa only [hT] using hlen')
  refine ⟨?_,?_⟩
  · simpa only [hT,he,topBlock,List.append_assoc] using hb
  · simpa only [hT,Real.log_pow] using hbsize

end GaussianMoat

end OAI
end
end

section
section
namespace OAI

namespace GaussianMoat
open scoped BigOperators Classical

theorem one_step_coverage (s : SplitSieve) (D : ℝ) (N : ℕ)
    (mid bot : List ℕ) (b q n : ℕ) (e ebase : ℝ)
    (u : s.SignedIndex → ℝ)
    (hm : EntropyBand s D mid 0 b e)
    (hb : EntropyBand s D bot N q ebase)
    (hb0 : 0<b) (hbk : b≤ s.primes.card) (hq0 : 0<q) (hqk : q≤ s.primes.card)
    (hN : 1≤bot.sum+N) (hn : 0<n)
    (hprime : ∀ i, Real.exp 100≤(s.signedPrime i:ℝ))
    (hu : ∀ i, 0<u i)
    (hbase : ebase*s.meanLog≤Real.exp (-100)/(512*640000))
    (hgap : e*s.meanLog+n*(Real.log 36+2*Real.log (D*(bot.sum+N)))/b<1/256)
    (herr : ∀ i, (s.signedPrime i:ℝ)*Real.exp
      (-(n:ℝ)*(1/64)^2*u i/(2*(s.signedPrime i:ℝ)))≤1/640000) :
    CoverageDerivation s D N (mid++bot) (1/4) u (1/100) := by
  let c : ℝ := Real.exp (-100)/512
  let u' : s.SignedIndex → ℝ := fun i => Real.exp (-100)/64*(s.signedPrime i:ℝ)
  let C : s.SignedIndex → ℝ := fun i => Real.exp (-100)*(s.signedPrime i:ℝ)
  have hc : 0<c := by dsimp [c]; positivity
  have htail : CoverageDerivation s D N bot (1/4+4*(1/64)) u' (1/640000) := by
    apply CoverageDerivation.base bot q (1/4+4*(1/64)) c ebase (1/640000) u' hb hq0 hqk
    · norm_num
    · exact hc
    · intro i; dsimp [c,u']; ring_nf; exact le_rfl
    · apply (div_le_iff₀ hc).mpr
      dsimp [c]
      linarith only [hbase]
  apply CoverageDerivation.step mid bot b n (1/4) (1/64) (1/640000) (1/100)
    (1/640000) e 100 u u' C hm htail hN hn hb0 hbk
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hu
  · norm_num
  · norm_num only [mul_one,one_mul,div_div]
    have hl2 : Real.log 2≤1 := by simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have hl : Real.log (12800:ℝ)≤14 := by
      have hh := Real.log_le_log (by norm_num : (0:ℝ)<12800) (by norm_num : (12800:ℝ)≤2^14)
      rw [Real.log_pow] at hh
      norm_num at hh
      linarith only [hh,hl2]
    rw [show (1:ℝ)/12800=(12800:ℝ)⁻¹ by rw [one_div],Real.log_inv]
    linarith only [hl]
  · norm_num only [Nat.cast_ofNat] at hgap ⊢
    convert hgap using 1
  · intro i
    have hh := mul_le_mul_of_nonneg_left (hprime i) (Real.exp_nonneg (-100))
    dsimp [C]
    rw [←Real.exp_add] at hh
    norm_num at hh
    exact hh
  · intro i
    dsimp [C]
    rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt ((Real.exp_pos 100).trans_le (hprime i))),Real.log_exp]
    linarith
  · intro i; dsimp [u',C]; ring_nf; exact le_rfl
  · exact herr

lemma package_list_arithmetic {X T p L n : ℝ} (hX : 1600≤X)
    (hT : Real.exp X≤T) (hp0 : 0<p) (hp : p≤2*T)
    (hn : 256*T*Real.log (2*T)≤n*L) :
    Real.log (4*(p*Real.exp (-X/200))+p*Real.exp (-(n:ℝ)*(L*((1/4)/p)/2)/4))≤
      Real.log p-X/400 := by
  have hX0 : 0≤X := by linarith only [hX]
  have hT0 : 0<T := (Real.exp_pos X).trans_le hT
  have hlog : X≤Real.log T := by
    exact (Real.log_exp X).symm ▸ Real.log_le_log (Real.exp_pos X) hT
  have hlog2 : X≤Real.log (2*T) := hlog.trans (Real.log_le_log hT0 (by linarith only [hT0]))
  have hl8 : Real.log 8≤3 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    rw [show (8:ℝ)=2^3 by norm_num,Real.log_pow]
    norm_num at hh ⊢
    linarith only [hh]
  have hhalf : 4*Real.exp (-X/200)≤Real.exp (-X/400)/2 := by
    have he : -X/200≤-X/400-Real.log 8 := by linarith only [hX,hl8]
    have hh := Real.exp_le_exp.mpr he
    rw [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<8)] at hh
    linarith only [hh]
  have hlarge : 4*Real.log (2*T)≤n*L/(32*p) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hp' := mul_le_mul_of_nonneg_right hp (show 0≤128*Real.log (2*T) by linarith only [hlog2,hX0])
    linarith only [hn,hp']
  have hsmall : Real.exp (-n*(L*((1/4)/p)/2)/4)≤Real.exp (-X/400)/2 := by
    have hl2 : Real.log 2≤1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      linarith only [hh]
    have he : -n*(L*((1/4)/p)/2)/4≤-X/400-Real.log 2 := by
      have heq : -n*(L*((1/4)/p)/2)/4= -(n*L/(32*p)) := by ring
      rw [heq]
      linarith only [hlarge,hlog2,hX,hl2]
    have hh := Real.exp_le_exp.mpr he
    rwa [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<2)] at hh
  have harg : 4*(p*Real.exp (-X/200))+p*Real.exp (-n*(L*((1/4)/p)/2)/4)≤
      p*Real.exp (-X/400) := by
    have h1 := mul_le_mul_of_nonneg_left hhalf hp0.le
    have h2 := mul_le_mul_of_nonneg_left hsmall hp0.le
    linarith only [h1,h2]
  have hh := Real.log_le_log (by positivity : 0<4*(p*Real.exp (-X/200))+p*Real.exp (-n*(L*((1/4)/p)/2)/4)) harg
  rw [Real.log_mul hp0.ne' (Real.exp_ne_zero _),Real.log_exp] at hh
  linarith only [hh]

lemma package_rate_arithmetic {X T L n b H E c mean : ℝ}
    (hX : 1≤X) (hT : 0<T) (hc : 0<c)
    (hlog : X≤Real.log T) (hlog' : Real.log T≤21/20*X)
    (hmean : mean≤2*X) (hb : c*T/Real.log T≤b)
    (hn : n*L≤1024*T*Real.log T)
    (hshift : 2*n*H≤c*T/5000) (hE : E≤c*T/10000) :
    n*(L*(c/(10000000*Real.log T))+2*H)≤
      b*((X/400)*(1-2*(1/100))-(1/10000)*mean)-E := by
  have hlog0 : 0<Real.log T := by linarith only [hX,hlog]
  have hb0 : 0<b := (div_pos (mul_pos hc hT) hlog0).trans_le hb
  have hbg : c*T≤b*Real.log T := (div_le_iff₀ hlog0).mp hb
  have hbg' : c*T≤b*(21/20*X) := hbg.trans (mul_le_mul_of_nonneg_left hlog' hb0.le)
  have hgain : X/500≤(X/400)*(1-2*(1/100))-(1/10000)*mean := by
    linarith only [hmean,hX]
  have hrev := mul_le_mul_of_nonneg_left hgain hb0.le
  have hcost := mul_le_mul_of_nonneg_right hn (show 0≤c/(10000000*Real.log T) by positivity)
  have heq : (1024*T*Real.log T)*(c/(10000000*Real.log T))=1024*c*T/10000000 := by
    field_simp
  rw [heq] at hcost
  linarith only [hbg',hrev,hcost,hshift,hE,mul_pos hc hT]

open scoped BigOperators Classical
open Filter

lemma eventually_poly_le_exp_linear (C : ℝ) {a : ℝ} (ha : 0<a) (d : ℕ) :
    ∀ᶠ X : ℝ in atTop, C*X^d≤Real.exp (a*X) := by
  have h := eventually_poly_le_exp (C/a^d) (a := 1) (by norm_num) d
  have ht : Tendsto (fun x : ℝ => a*x) atTop atTop := tendsto_id.const_mul_atTop ha
  filter_upwards [ht.eventually h] with X hX
  simp only [one_mul,mul_pow] at hX
  convert hX using 1; field_simp

lemma eventually_mul_exp_le_exp {a b : ℝ} (hab : a<b) (C : ℝ) :
    ∀ᶠ X : ℝ in atTop, C*Real.exp (a*X)≤Real.exp (b*X) := by
  have h := eventually_poly_le_exp_linear C (sub_pos.mpr hab) 0
  filter_upwards [h] with X hX
  simp only [pow_zero,mul_one] at hX
  have hh := mul_le_mul_of_nonneg_right hX (Real.exp_nonneg (a*X))
  rw [←Real.exp_add] at hh
  convert hh using 1
  congr 1
  ring_nf

noncomputable def batchWordLength (j : ℕ) : ℕ := 2^(2*j/5)
noncomputable def packageRepetitions (j : ℕ) : ℕ :=
  ⌈256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)/batchWordLength j⌉₊

lemma batchWordLength_pos (j : ℕ) : 0<batchWordLength j := by
  unfold batchWordLength; positivity

lemma batchWordLength_dvd {i j : ℕ} (hij : i≤j) : batchWordLength i∣batchWordLength j := by
  exact pow_dvd_pow 2 (Nat.div_le_div_right (Nat.mul_le_mul_left 2 hij))

lemma batchWordLength_log (j : ℕ) :
    (2/5:ℝ)*(j*Real.log 2)-Real.log 2≤Real.log (batchWordLength j:ℝ) ∧
    Real.log (batchWordLength j:ℝ)≤(2/5:ℝ)*(j*Real.log 2) := by
  have hp : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have h1 : 5*(2*j/5)≤2*j := Nat.mul_div_le _ _
  have h2 : 2*j<5*(2*j/5+1) := Nat.lt_mul_div_succ _ (by norm_num)
  have h1' : 5*(2*j/5:ℕ)≤(2:ℝ)*j := by exact_mod_cast h1
  have h2' : (2:ℝ)*j<5*((2*j/5:ℕ)+1) := by exact_mod_cast h2
  have hh1 := mul_le_mul_of_nonneg_right h1' hp.le
  have hh2 := mul_lt_mul_of_pos_right h2' hp
  simp only [batchWordLength,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  constructor <;> linarith only [hh1,hh2]

lemma batchWordLength_le_scale (j : ℕ) : (batchWordLength j:ℝ)≤(2:ℝ)^j := by
  unfold batchWordLength
  push_cast
  apply pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
  omega

theorem eventually_integer_batch_bounds {D : ℝ} (hD : 1≤D) :
    ∀ᶠ X : ℝ in atTop, ∀ j : ℕ,
      X≤j*Real.log 2 → j*Real.log 2≤21/20*X →
      0<packageRepetitions j ∧
      (D*(batchWordLength j:ℝ))^2<(2:ℝ)^j ∧
      256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)≤
        (packageRepetitions j:ℝ)*batchWordLength j ∧
      (packageRepetitions j:ℝ)*batchWordLength j≤1024*(2:ℝ)^j*Real.log ((2:ℝ)^j) ∧
      (packageRepetitions j:ℝ)≤Real.exp (7/10*X) ∧
      (batchWordLength j:ℝ)≤Real.exp (21/50*X) := by
  have hpoly := eventually_poly_le_exp_linear (1024:ℝ) (a := 1/100) (by norm_num) 1
  have hshort' := eventually_mul_exp_le_exp (a := 0) (b := 4/25) (by norm_num) (2*D^2)
  filter_upwards [hpoly,hshort',eventually_ge_atTop (100:ℝ)] with X hpoly hshort' hX
  intro j hlo hhi
  have hl2 : Real.log (2:ℝ)≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith only [hh]
  have hT : Real.log ((2:ℝ)^j)=(j:ℝ)*Real.log 2 := Real.log_pow _ _
  have hTpos : 0<(2:ℝ)^j := by positivity
  have hLpos : 0<(batchWordLength j:ℝ) := by exact_mod_cast batchWordLength_pos j
  have hLlog := batchWordLength_log j
  have hLlo : Real.exp (39/100*X)≤(batchWordLength j:ℝ) := by
    rw [←Real.exp_log hLpos]
    apply Real.exp_le_exp.mpr
    linarith only [hLlog.1,hlo,hl2,hX]
  have hLhi : (batchWordLength j:ℝ)≤Real.exp (21/50*X) := by
    rw [←Real.exp_log hLpos]
    apply Real.exp_le_exp.mpr
    linarith only [hLlog.2,hhi]
  have hThe : (2:ℝ)^j≤Real.exp (21/20*X) := by
    rw [←Real.exp_log hTpos,hT]
    exact Real.exp_le_exp.mpr hhi
  have hTel : Real.exp X≤(2:ℝ)^j := by
    rw [←Real.exp_log hTpos,hT]
    exact Real.exp_le_exp.mpr hlo
  have hlogT : 1≤Real.log ((2:ℝ)^j) := by rw [hT]; linarith only [hlo,hX]
  have hlog2T : Real.log (2*(2:ℝ)^j)=Real.log 2+Real.log ((2:ℝ)^j) :=
    Real.log_mul (by norm_num) hTpos.ne'
  have hnum : 0<256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j) := by
    rw [hlog2T]; positivity
  have hnlo : 256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)≤
      (packageRepetitions j:ℝ)*batchWordLength j := by
    exact (div_le_iff₀ hLpos).mp (Nat.le_ceil _)
  have hnhi : (packageRepetitions j:ℝ)*batchWordLength j≤
      256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)+(batchWordLength j:ℝ) := by
    have hh := (Nat.ceil_lt_add_one (show 0≤256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)/batchWordLength j by positivity)).le
    have hm := mul_le_mul_of_nonneg_right hh hLpos.le
    rw [add_mul,one_mul,div_mul_cancel₀ _ hLpos.ne'] at hm
    exact hm
  have hprod : (packageRepetitions j:ℝ)*batchWordLength j≤1024*(2:ℝ)^j*Real.log ((2:ℝ)^j) := by
    have hL := batchWordLength_le_scale j
    rw [hlog2T] at hnhi
    have hh := mul_le_mul_of_nonneg_left hl2 (show 0≤256*(2:ℝ)^j by positivity)
    have hh' := mul_le_mul_of_nonneg_left hlogT (show 0≤(2:ℝ)^j by positivity)
    linarith only [hnhi,hL,hh,hh',hTpos]
  have hnbound : (packageRepetitions j:ℝ)≤Real.exp (7/10*X) := by
    have hrough : (packageRepetitions j:ℝ)*(batchWordLength j:ℝ)≤
        1024*Real.exp (21/20*X)*(21/20*X) := by
      apply hprod.trans
      gcongr
      rw [hT]; exact hhi
    have hn' := mul_le_mul_of_nonneg_left hLlo (Nat.cast_nonneg (packageRepetitions j))
    have hc : 1024*(21/20*X)≤Real.exp (4/100*X) := by
      have he := Real.add_one_le_exp (3/100*X)
      have he' : (21/20:ℝ)≤Real.exp (3/100*X) := by linarith only [he,hX]
      have hm := mul_le_mul hpoly he' (by norm_num) (Real.exp_nonneg _)
      simp only [pow_one] at hm
      rw [←Real.exp_add] at hm
      rw [show 1/100*X+3/100*X=4/100*X by ring] at hm
      linarith only [hm]
    have hh := mul_le_mul_of_nonneg_right hc (Real.exp_nonneg (21/20*X))
    rw [←Real.exp_add] at hh
    have hlast : (packageRepetitions j:ℝ)*Real.exp (39/100*X)≤
        Real.exp (7/10*X)*Real.exp (39/100*X) := by
      apply hn'.trans (hrough.trans _)
      rw [←Real.exp_add]
      rw [show 4/100*X+21/20*X=7/10*X+39/100*X by ring] at hh
      linarith only [hh]
    nlinarith only [hlast,Real.exp_pos (39/100*X)]
  refine ⟨?_,?_,hnlo,hprod,hnbound,hLhi⟩
  · exact Nat.ceil_pos.mpr (div_pos hnum hLpos)
  · have hsquare := mul_le_mul hLhi hLhi hLpos.le (Real.exp_nonneg _)
    rw [←Real.exp_add] at hsquare
    have hh := mul_le_mul_of_nonneg_left hsquare (sq_nonneg D)
    have hstrict : D^2<Real.exp (4/25*X) := by
      simp only [zero_mul,Real.exp_zero,mul_one] at hshort'
      have hDpos : 0<D^2 := sq_pos_of_pos (by linarith only [hD])
      linarith only [hshort',hDpos]
    have hs := mul_lt_mul_of_pos_right hstrict (Real.exp_pos (21/50*X+21/50*X))
    rw [←Real.exp_add] at hs
    have he : 4/25*X+(21/50*X+21/50*X)=X := by ring
    rw [he] at hs
    have hsq : (D*(batchWordLength j:ℝ))^2≤D^2*Real.exp (21/50*X+21/50*X) := by
      linarith only [hh]
    exact (hsq.trans_lt hs).trans_le hTel

end GaussianMoat

end OAI
end
end

section
section
namespace OAI

namespace GaussianMoat
open scoped BigOperators Classical
open Filter

lemma window_power_step {i w : ℕ} (hi : i<w) :
    (100:ℝ)^i≤(100:ℝ)^w/100 := by
  have hh : (100:ℝ)^(i+1)≤(100:ℝ)^w := pow_le_pow_right₀ (by norm_num) hi
  rw [pow_succ] at hh
  linarith only [hh]

lemma window_power_nonneg (w : ℕ) : (0:ℝ)≤100^w := by positivity
lemma window_power_one (w : ℕ) : (1:ℝ)≤100^w := one_le_pow₀ (by norm_num)

lemma smaller_window_operations {a : ℝ} (ha : 0≤a) (ha1 : a≤1)
    (m w : ℕ) (J : ℕ → Finset ℕ)
    (hJ : ∀ i<w, ∀ j∈J i, (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m)) :
    ∀ n∈windowBlocks a m J w,
      (n:ℝ)≤Real.exp (Real.exp (((100:ℝ)^w/50)*Real.exp m)) := by
  intro n hn
  obtain ⟨i,hi,hni⟩ := windowBlocks_mem a m J hn
  have hh := mul_le_mul_of_nonneg_right (window_power_step hi) (Real.exp_nonneg (m:ℝ))
  have hi0 : 0≤(100:ℝ)^i*Real.exp m := by positivity
  rcases hni with hni|hni
  · obtain ⟨j,hj,hnj⟩ := List.mem_flatMap.mp hni
    have hj' : j∈J i := (Finset.mem_sort (·≥·)).mp hj
    have hp : (2:ℝ)^j≤Real.exp (((100:ℝ)^w/50)*Real.exp m) := by
      rw [←Real.exp_log (by positivity : (0:ℝ)<2^j),Real.log_pow]
      apply Real.exp_le_exp.mpr
      linarith only [hJ i hi j hj',hh,hi0]
    apply topBlock_bound ha j _ n hnj
    have hc : topParameter*a≤1 := by
      have hg : topParameter≤1 := by norm_num [topParameter]
      exact (mul_le_mul_of_nonneg_left ha1 topParameter_pos.le).trans (by simpa only [mul_one] using hg)
    exact (mul_le_of_le_one_left (by positivity : (0:ℝ)≤2^j) hc).trans hp
  · apply accurateBlock_bound (accurateGrid_le_one m) _ n hni
    have he : Real.exp (((100:ℝ)^i/4)*Real.exp m)≤Real.exp (((100:ℝ)^w/50)*Real.exp m) := by
      apply Real.exp_le_exp.mpr
      linarith only [hh,hi0]
    exact (mul_le_of_le_one_left (Real.exp_nonneg _) (accurateGrid_le_one m)).trans he

lemma windowBlocks_length_bound {C : ℝ} {a : ℝ} (m W : ℕ)
    (J : ℕ → Finset ℕ) (hJ : ∀ w<W, ((J w).card:ℝ)≤C) :
    ((windowBlocks a m J W).length:ℝ)≤(W:ℝ)*(20*C+4*(m:ℝ)^2) := by
  induction W with
  | zero => simp [windowBlocks]
  | succ W ih =>
    have hi := ih (fun w hw => hJ w (by omega))
    rw [windowBlocks_succ,List.length_append,List.length_append]
    simp only [topBlocks_length,Nat.cast_add,Nat.cast_mul,topIterations,Nat.cast_ofNat,
      accurateBlock,List.length_ofFn,accurateIterations,Nat.cast_pow]
    have hh := hJ W (by omega)
    have hW : (W:ℝ)+1=(W+1:ℕ) := by push_cast; rfl
    push_cast
    linarith only [hi,hh]

lemma windowBlocks_length_bound_of_bins {a : ℝ} {m W : ℕ}
    (J : ℕ → Finset ℕ) (hm : 2≤Real.exp m)
    (hJ : ∀ w<W, ∀ j∈J w, (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) :
    ((windowBlocks a m J W).length:ℝ)≤
      (W:ℝ)*(60*(100:ℝ)^W*Real.exp m+4*(m:ℝ)^2) := by
  have hb : ∀ w<W, ((J w).card:ℝ)≤3*(100:ℝ)^W*Real.exp m := by
    intro w hw
    have hw1 := window_power_one w
    have hs : 2≤(100:ℝ)^w*Real.exp m := by nlinarith only [hw1,hm]
    have hh := narrow_bins_card hs (J w) (hJ w hw)
    have hp : (100:ℝ)^w≤(100:ℝ)^W := pow_le_pow_right₀ (by norm_num) hw.le
    have he := mul_le_mul_of_nonneg_right hp (Real.exp_nonneg (m:ℝ))
    linarith only [hh,he]
  have hh := windowBlocks_length_bound (a := a) m W J hb
  linarith only [hh]

lemma eventually_window_length (W : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      (W:ℝ)*(60*(100:ℝ)^W*Real.exp m+4*(m:ℝ)^2)+4*(m:ℝ)^2+2≤Real.exp (Real.exp m) := by
  have hp := eventually_poly_le_exp (4*((W:ℝ)+1)) (a := 1) (by norm_num) 2
  have ht := (eventually_mul_le_double_exp (a := 1) (by norm_num) (60*W*(100:ℝ)^W+3))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hp,ht] with m hm ht
  simp only [one_mul] at hm ht
  have he : 1≤Real.exp (m:ℝ) := Real.one_le_exp_iff.mpr (Nat.cast_nonneg _)
  linarith only [hm,ht,he]

noncomputable def windowSmoothing (W m : ℕ) : ℕ :=
  ⌈Real.exp (20*(100:ℝ)^W*Real.exp m)⌉₊

lemma windowSmoothing_pos (W m : ℕ) : 0<windowSmoothing W m :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

lemma windowSmoothing_bounds (W m : ℕ) :
    Real.exp (20*(100:ℝ)^W*Real.exp m)≤(windowSmoothing W m:ℝ) ∧
    (windowSmoothing W m:ℝ)+1≤Real.exp ((20*(100:ℝ)^W+2)*Real.exp m) := by
  refine ⟨Nat.le_ceil _,?_⟩
  have hh := (Nat.ceil_lt_add_one (Real.exp_nonneg (20*(100:ℝ)^W*Real.exp m))).le
  have he : 1≤Real.exp (m:ℝ) := Real.one_le_exp_iff.mpr (Nat.cast_nonneg _)
  have he' : 3≤Real.exp (2*Real.exp (m:ℝ)) := by
    have hh := Real.add_one_le_exp (2*Real.exp (m:ℝ))
    linarith only [hh,he]
  have hbase : 1≤Real.exp (20*(100:ℝ)^W*Real.exp m) := Real.one_le_exp_iff.mpr (by positivity)
  have hmul := mul_le_mul_of_nonneg_left he' (Real.exp_nonneg (20*(100:ℝ)^W*Real.exp m))
  rw [←Real.exp_add] at hmul
  change (⌈Real.exp (20*(100:ℝ)^W*Real.exp m)⌉₊:ℝ)+1≤_
  rw [show (20*(100:ℝ)^W+2)*Real.exp m=20*(100:ℝ)^W*Real.exp m+2*Real.exp m by ring]
  linarith only [hh,hbase,hmul]

theorem eventually_suffix_cost {D a b C : ℝ} (hD : 0<D) (ha : 0<a) (hab : a<b) :
    ∀ᶠ X : ℝ in atTop, ∀ ns : List ℕ, ∀ N : ℕ,
      1≤ns.sum+N → (ns.length+2:ℝ)≤Real.exp X →
      (∀ n∈ns, (n:ℝ)≤Real.exp (Real.exp (a*X))) →
      (N:ℝ)+1≤Real.exp (C*X) →
      Real.log 36+2*Real.log (D*(ns.sum+N))≤Real.exp (b*X) := by
  have hp := eventually_poly_le_exp_linear
    (|Real.log 36|+2*|Real.log D|+2*|1+C|) ha 1
  have hres := eventually_mul_exp_le_exp hab 3
  filter_upwards [hp,hres,eventually_ge_atTop (1:ℝ)] with X hp hres hX
  intro ns N hs hl ho hN
  have hlog := schedule_log_bound ns N (Real.exp_nonneg (a*X)) ho
  have hl' : Real.log ((ns.length:ℝ)+1)≤X := by
    have hh := Real.log_le_log (by positivity : 0<(ns.length:ℝ)+1) (by linarith only [hl] : (ns.length:ℝ)+1≤Real.exp X)
    rwa [Real.log_exp] at hh
  have hN' : Real.log ((N:ℝ)+1)≤C*X := by
    have hh := Real.log_le_log (by positivity : 0<(N:ℝ)+1) hN
    rwa [Real.log_exp] at hh
  have hspos : (0:ℝ)<(ns.sum+N:ℕ) := by exact_mod_cast (show 0<ns.sum+N by omega)
  have hs' : Real.log ((ns.sum+N:ℕ):ℝ)≤Real.log ((ns.sum+N:ℕ)+1) :=
    Real.log_le_log hspos (by push_cast; linarith)
  simp only [Nat.cast_add] at hspos hs' hlog
  rw [Real.log_mul hD.ne' hspos.ne']
  have hc : Real.log 36+2*Real.log D+2*(1+C)*X≤Real.exp (a*X) := by
    simp only [pow_one] at hp
    have h1 := le_abs_self (Real.log (36:ℝ))
    have h2 := le_abs_self (Real.log D)
    have h3 := le_abs_self (1+C)
    nlinarith only [hp,hX,h1,h2,h3,abs_nonneg (Real.log (36:ℝ)),abs_nonneg (Real.log D)]
  linarith only [hlog,hl',hN',hs',hc,hres]

noncomputable def coverageRepetitions (X : ℝ) : ℕ := ⌈Real.exp (X/100)⌉₊

lemma coverageRepetitions_pos (X : ℝ) : 0<coverageRepetitions X :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

lemma coverageRepetitions_bounds {X : ℝ} (hX : 0≤X) :
    Real.exp (X/100)≤(coverageRepetitions X:ℝ) ∧
    (coverageRepetitions X:ℝ)≤2*Real.exp (X/100) := by
  refine ⟨Nat.le_ceil _,?_⟩
  have hh := (Nat.ceil_lt_add_one (Real.exp_nonneg (X/100))).le
  have he : 1≤Real.exp (X/100) := Real.one_le_exp_iff.mpr (by positivity)
  change (⌈Real.exp (X/100)⌉₊:ℝ)≤2*Real.exp (X/100)
  linarith only [hh,he]

lemma eventually_coverage_hazard :
    ∀ᶠ X : ℝ in atTop, ∀ p : ℝ, 0<p → p≤2*Real.exp (21/20*X) →
      p*Real.exp (-(coverageRepetitions X:ℝ)*(1/64)^2*
        (p*Real.exp (-X/200))/(2*p))≤1/640000 := by
  have hp := eventually_poly_le_exp_linear (8192*(21/20+Real.log (1280000:ℝ)))
    (a := 1/200) (by norm_num) 1
  filter_upwards [hp,eventually_ge_atTop (1:ℝ)] with X hpoly hX
  intro p hp0 hp
  have hlog : 0≤Real.log (1280000:ℝ) := Real.log_nonneg (by norm_num)
  have hmargin : 8192*(21/20*X+Real.log (1280000:ℝ))≤Real.exp (X/200) := by
    simp only [pow_one,show (1:ℝ)/200*X=X/200 by ring] at hpoly
    nlinarith only [hpoly,hX,hlog]
  have hn := (coverageRepetitions_bounds (by linarith only [hX])).1
  have hn' := mul_le_mul_of_nonneg_right hn (Real.exp_nonneg (-X/200))
  rw [←Real.exp_add] at hn'
  have he : X/100+-X/200=X/200 := by ring
  rw [he] at hn'
  have harg : -(coverageRepetitions X:ℝ)*(1/64)^2*(p*Real.exp (-X/200))/(2*p)≤
      -(21/20*X)-Real.log (1280000:ℝ) := by
    have hEq : -(coverageRepetitions X:ℝ)*(1/64)^2*(p*Real.exp (-X/200))/(2*p)=
        -(coverageRepetitions X:ℝ)*Real.exp (-X/200)/8192 := by field_simp; ring
    rw [hEq]
    linarith only [hmargin,hn']
  have hh := mul_le_mul hp (Real.exp_le_exp.mpr harg) (Real.exp_nonneg _) (by positivity : 0≤2*Real.exp (21/20*X))
  simp only [mul_assoc,←Real.exp_add] at hh
  have he' : 21/20*X+(-(21/20*X)-Real.log (1280000:ℝ))=-Real.log (1280000:ℝ) := by ring
  rw [he',Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<1280000)] at hh
  norm_num at hh ⊢
  simpa only [mul_assoc] using hh

lemma eventually_coverage_data_cost :
    ∀ᶠ X : ℝ in atTop, ∀ H b : ℝ,
      H≤Real.exp (3/50*X) → Real.exp (X/8)/(4*X)≤b →
      (coverageRepetitions X:ℝ)*H/b≤1/1024 := by
  have hp := eventually_poly_le_exp_linear (8192:ℝ) (a := 11/200) (by norm_num) 1
  filter_upwards [hp,eventually_ge_atTop (1:ℝ)] with X hpoly hX
  intro H b hH hb
  have hXp : 0<X := by linarith only [hX]
  have hbp : 0<b := (div_pos (Real.exp_pos _) (by positivity)).trans_le hb
  have hn := (coverageRepetitions_bounds hXp.le).2
  have hmul := (mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg (coverageRepetitions X))).trans
    (mul_le_mul_of_nonneg_right hn (Real.exp_nonneg (3/50*X)))
  simp only [mul_assoc,←Real.exp_add] at hmul
  have hEq : X/100+3/50*X=7/100*X := by ring
  rw [hEq] at hmul
  have hb' := (div_le_iff₀ (show 0<4*X by positivity)).mp hb
  simp only [pow_one] at hpoly
  have hh := mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg (7/100*X))
  rw [←Real.exp_add] at hh
  have he : 11/200*X+7/100*X=X/8 := by ring
  rw [he] at hh
  have hnH : (coverageRepetitions X:ℝ)*H*(4096*X)≤b*(4*X) := by
    have hh' := mul_le_mul_of_nonneg_right hmul (show 0≤4096*X by positivity)
    linarith only [hh',hh,hb']
  apply (div_le_iff₀ hbp).mpr
  nlinarith only [hnH,hXp]

lemma eventually_package_displacement {c : ℝ} (hc : 0<c) :
    ∀ᶠ X : ℝ in atTop, ∀ n H T : ℝ,
      0≤n → n≤Real.exp (7/10*X) → H≤Real.exp (13/50*X) → Real.exp X≤T →
      2*n*H≤c*T/5000 := by
  have hh := eventually_mul_exp_le_exp (a := 24/25) (b := 1) (by norm_num) (10000/c)
  filter_upwards [hh] with X hX
  intro n H T hn0 hn hH hT
  have hmul := (mul_le_mul_of_nonneg_left hH hn0).trans
    (mul_le_mul_of_nonneg_right hn (Real.exp_nonneg (13/50*X)))
  rw [←Real.exp_add] at hmul
  have he : 7/10*X+13/50*X=24/25*X := by ring
  rw [he] at hmul
  simp only [one_mul] at hX
  have hh' := mul_le_mul_of_nonneg_left (hX.trans hT) hc.le
  rw [←mul_assoc,mul_div_cancel₀ _ hc.ne'] at hh'
  linarith only [hmul,hh']

theorem coverage_from_scalar_guards (s : SplitSieve) (D X : ℝ) (N : ℕ)
    (mid bot : List ℕ) (b q : ℕ) (e : ℝ)
    (hm : EntropyBand s D mid 0 b e) (hb : EntropyBand s D bot N q e)
    (hmean : 0< s.meanLog) (hN : 1≤bot.sum+N)
    (hX : 100≤X)
    (hp : ∀ i, Real.exp X≤(s.signedPrime i:ℝ) ∧
      (s.signedPrime i:ℝ)≤2*Real.exp (21/20*X))
    (hbase : e*s.meanLog≤Real.exp (-100)/(512*640000))
    (hmid : e*s.meanLog≤1/1024)
    (hcost : (coverageRepetitions X:ℝ)*(Real.log 36+2*Real.log (D*(bot.sum+N)))/b≤1/1024)
    (hhazard : ∀ i, (s.signedPrime i:ℝ)*Real.exp
      (-(coverageRepetitions X:ℝ)*(1/64)^2*
        ((s.signedPrime i:ℝ)*Real.exp (-X/200))/(2*(s.signedPrime i:ℝ)))≤1/640000) :
    CoverageDerivation s D N (mid++bot) (1/4)
      (fun i => (s.signedPrime i:ℝ)*Real.exp (-X/200)) (1/100) := by
  exact one_step_coverage s D N mid bot b q (coverageRepetitions X) e e _ hm hb
    (hm.size_pos hmean) (hm.size_cap hmean) (hb.size_pos hmean) (hb.size_cap hmean)
    hN (coverageRepetitions_pos X)
    (fun i => (Real.exp_le_exp.mpr hX).trans (hp i).1)
    (fun i => mul_pos ((Real.exp_pos X).trans_le (hp i).1) (Real.exp_pos _)) hbase
    (by linarith only [hmid,hcost]) hhazard

lemma binEntropy_small_exp {t Y : ℝ} (ht : 0≤t) (hY : 1≤Y)
    (htY : t≤Real.exp (-Y)) :
    Real.binEntropy t≤(Y+1)*Real.exp (-Y) := by
  have heY : 2≤Real.exp Y := by linarith only [Real.add_one_le_exp Y,hY]
  have hu : Real.exp (-Y)≤(1/2:ℝ) := by
    rw [Real.exp_neg]
    exact inv_le_of_inv_le₀ (by norm_num) (by simpa using heY)
  have hm := Real.binEntropy_strictMonoOn.monotoneOn
    (show t∈Set.Icc 0 (2:ℝ)⁻¹ by norm_num; exact ⟨ht,htY.trans hu⟩)
    (show Real.exp (-Y)∈Set.Icc 0 (2:ℝ)⁻¹ by norm_num; exact ⟨(Real.exp_pos _).le,hu⟩) htY
  have hn := Real.negMulLog_le_one_sub_self (show 0≤1-Real.exp (-Y) by linarith only [hu])
  simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    Real.negMulLog,Real.log_exp] at hm ⊢
  have hh : -(1-Real.exp (-Y))*Real.log (1-Real.exp (-Y))≤Real.exp (-Y) := by
    simpa only [Real.negMulLog,sub_sub_cancel] using hn
  linarith only [hm,hh]

lemma exp_ratio_bound {a N X A : ℝ} (ha : a≤Real.exp (A*X))
    (hN : Real.exp (10*A*X)≤N) :
    a/(N+1)≤Real.exp (-9*A*X) := by
  have hNp : 0<N+1 := by linarith only [hN,Real.exp_pos (10*A*X)]
  apply (div_le_iff₀ hNp).mpr
  have hh := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg (-9*A*X))
  rw [←Real.exp_add] at hh
  rw [show -9*A*X+10*A*X=A*X by ring] at hh
  linarith only [ha,hh,Real.exp_nonneg (-9*A*X)]

theorem eventually_smoothing_guard {A H : ℝ} (hA : 1≤A) :
    ∀ᶠ X : ℝ in atTop, ∀ a L E N : ℝ,
      0≤a → a≤Real.exp (A*X) → 0≤L → L≤Real.exp (A*X) →
      E≤Real.exp (A*X) → Real.exp (10*A*X)≤N →
      2*Real.binEntropy (a/(N+1))+(a/(N+1))*(L*H+2*E)≤Real.exp (-X) := by
  have hpoly := eventually_poly_le_exp_linear (4*(9*A+1))
    (a := 9*A-1) (by linarith only [hA]) 1
  have hcost := eventually_poly_le_exp_linear (2*(max H 0+2))
    (a := 8*A-1) (by linarith only [hA]) 0
  filter_upwards [hpoly,hcost,eventually_ge_atTop (1:ℝ)] with X hpoly hcost hX
  intro a L E N ha0 ha hL0 hL hE hN
  have hNpos : 0<N+1 := by linarith only [hN,Real.exp_pos (10*A*X)]
  have ht0 : 0≤a/(N+1) := div_nonneg ha0 hNpos.le
  have ht := exp_ratio_bound ha hN
  have hAX : 1≤A*X := by nlinarith only [hA,hX]
  have hbin := binEntropy_small_exp ht0 (by linarith only [hAX] : 1≤9*A*X)
    (by simpa only [neg_mul] using ht)
  have hbin' : 2*Real.binEntropy (a/(N+1))≤Real.exp (-X)/2 := by
    simp only [pow_one] at hpoly
    have hc : 4*(9*A*X+1)≤Real.exp ((9*A-1)*X) := by linarith only [hpoly,hX]
    have hh := mul_le_mul_of_nonneg_right hc (Real.exp_nonneg (-(9*A*X)))
    rw [←Real.exp_add,show (9*A-1)*X+-(9*A*X)= -X by ring] at hh
    linarith only [hh,hbin]
  have hK : L*H+2*E≤(max H 0+2)*Real.exp (A*X) := by
    have hh := mul_le_mul_of_nonneg_left (le_max_left H 0) hL0
    have hh' := mul_le_mul_of_nonneg_right hL (le_max_right H 0)
    linarith only [hh,hh',hE]
  have hKt := (mul_le_mul_of_nonneg_left hK ht0).trans
    (mul_le_mul_of_nonneg_right ht (show 0≤(max H 0+2)*Real.exp (A*X) by positivity))
  have hprod : Real.exp (-9*A*X)*((max H 0+2)*Real.exp (A*X))=
      (max H 0+2)*Real.exp (-8*A*X) := by
    rw [mul_left_comm,←Real.exp_add]
    congr 1
    ring_nf
  rw [hprod] at hKt
  have hlast : (max H 0+2)*Real.exp (-8*A*X)≤Real.exp (-X)/2 := by
    simp only [pow_zero,mul_one] at hcost
    have hh := mul_le_mul_of_nonneg_right hcost (Real.exp_nonneg (-8*A*X))
    rw [←Real.exp_add,show (8*A-1)*X+-8*A*X= -X by ring] at hh
    linarith only [hh]
  linarith only [hbin',hKt,hlast]

lemma eventually_smoothing_total (C : ℝ) :
    ∀ᶠ X : ℝ in atTop, C*X*Real.exp (-X)≤1 := by
  have hh := eventually_poly_le_exp C (a := 1) (by norm_num) 1
  filter_upwards [hh] with X hX
  simp only [pow_one,one_mul] at hX
  have hm := mul_le_mul_of_nonneg_right hX (Real.exp_nonneg (-X))
  simpa only [←Real.exp_add,add_neg_cancel,Real.exp_zero] using hm

end GaussianMoat

end OAI
end
end

section
section
namespace OAI

namespace GaussianMoat
open scoped BigOperators Classical
open Filter

noncomputable def commonBlocks (a : ℝ) (m W : ℕ) (J : ℕ → Finset ℕ) : List ℕ :=
  windowBlocks a m J W++accurateBlock m (1/20)

noncomputable def middleBlocks (a : ℝ) (m w : ℕ) (J : ℕ → Finset ℕ) : List ℕ :=
  accurateBlock m ((100:ℝ)^w/4)++windowBlocks a m J w

lemma windowScale_tendsto (w : ℕ) :
    Tendsto (fun m : ℕ => (100:ℝ)^w*Real.exp m) atTop atTop :=
  (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)

lemma dyadic_prime_bounds (j : ℕ) :
    ∀ p∈(dyadicSieve j).primes, (2:ℝ)^j≤(p:ℝ) ∧ (p:ℝ)≤2*(2:ℝ)^j := by
  intro p hp
  have hh := (PrimeLogMass.mem_dyadicBatch j p).mp hp
  constructor
  · exact_mod_cast hh.1
  · have hh' : p≤2^(j+1) := hh.2.1.le
    rw [pow_succ] at hh'
    exact_mod_cast (by simpa only [mul_comm] using hh' : p≤2*2^j)

lemma dyadic_dense_nonempty {δ : ℝ} (hδ : 0<δ) {j : ℕ}
    (hd : δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(PrimeLogMass.dyadicBatch j).card) :
    (dyadicSieve j).primes.Nonempty := by
  apply Finset.card_pos.mp
  have hp : 0<δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1)) := by rw [Real.log_pow]; positivity
  exact_mod_cast hp.trans_le hd

lemma dyadic_mean_bounds {X : ℝ} (hX : 2≤X) {j : ℕ}
    (hne : (dyadicSieve j).primes.Nonempty)
    (hlo : X≤j*Real.log 2) (hhi : j*Real.log 2≤21/20*X) :
    1≤(dyadicSieve j).meanLog ∧ (dyadicSieve j).meanLog≤2*X := by
  have hh := (dyadicSieve j).meanLog_bounds hne (by positivity) (dyadic_prime_bounds j)
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hh
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  constructor <;> linarith only [hh.1,hh.2,hlo,hhi,hX,hl2]

lemma commonBlocks_length {a : ℝ} {m W : ℕ} (J : ℕ → Finset ℕ) (hm : 2≤Real.exp m)
    (hJ : ∀ w<W, ∀ j∈J w, (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) :
    ((commonBlocks a m W J).length:ℝ)+2≤
      (W:ℝ)*(60*(100:ℝ)^W*Real.exp m+4*(m:ℝ)^2)+4*(m:ℝ)^2+2 := by
  have hh := windowBlocks_length_bound_of_bins (a := a) J hm hJ
  simp only [commonBlocks,List.length_append,accurateBlock,List.length_ofFn,
    accurateIterations,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  linarith only [hh]

lemma middleBlocks_length_le {a : ℝ} {m W w : ℕ} (J : ℕ → Finset ℕ) (hw : w<W) :
    (middleBlocks a m w J).length≤(windowBlocks a m J W).length := by
  obtain ⟨pre,he⟩ := windowBlocks_split a m J hw
  simp only [middleBlocks,he,List.length_append]
  omega

theorem eventually_window_tail_bounds {D a : ℝ} (hD : 1≤D) (ha : 0≤a) (ha1 : a≤1)
    (W w : ℕ) (hw : w<W) :
    ∀ᶠ m : ℕ in atTop, ∀ J : ℕ → Finset ℕ,
      (∀ i<W, ∀ j∈J i, (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m)) →
      ((commonBlocks a m W J).length:ℝ)+2≤Real.exp (Real.exp m) ∧
      (windowSmoothing W m:ℝ)≤Real.exp (Real.exp ((1/100)*Real.exp m)) ∧
      ((windowBlocks a m J w).length+2:ℝ)≤Real.exp (Real.exp (((100:ℝ)^w/50)*Real.exp m)) ∧
      Real.log 36+2*Real.log (D*((accurateBlock m (1/20)).sum+windowSmoothing W m))≤
        Real.exp (3/50*((100:ℝ)^w*Real.exp m)) ∧
      Real.log 36+2*Real.log (D*((middleBlocks a m w J++accurateBlock m (1/20)).sum+windowSmoothing W m))≤
        Real.exp (13/50*((100:ℝ)^w*Real.exp m)) := by
  have hN := eventually_mul_le_double_exp (a := 1/100) (by norm_num) (20*(100:ℝ)^W+2)
  have hlen := eventually_mul_le_double_exp (a := 1/100) (by norm_num) 1
  have ht := windowScale_tendsto w
  have hbot := ht.eventually (eventually_suffix_cost (D := D) (a := 1/20) (b := 3/50)
    (C := 20*(100:ℝ)^W+2) (by linarith only [hD]) (by norm_num) (by norm_num))
  have hrest := ht.eventually (eventually_suffix_cost (D := D) (a := 1/4) (b := 13/50)
    (C := 20*(100:ℝ)^W+2) (by linarith only [hD]) (by norm_num) (by norm_num))
  have hm2 := (windowScale_tendsto 0).eventually (eventually_ge_atTop (2:ℝ))
  filter_upwards [eventually_window_length W,hN,hlen,hbot,hrest,hm2] with m hm hN hlen hbot hrest hm2
  intro J hJ
  simp only [one_mul] at hlen
  simp only [pow_zero,one_mul] at hm2
  have hl := (commonBlocks_length (a := a) J hm2 hJ).trans hm
  have hpow := window_power_one w
  have hX : Real.exp (m:ℝ)≤(100:ℝ)^w*Real.exp m := by nlinarith only [hpow,Real.exp_pos (m:ℝ)]
  have hNsmall : (windowSmoothing W m:ℝ)≤Real.exp (Real.exp ((1/100)*Real.exp m)) := by
    have hN' := (windowSmoothing_bounds W m).2.trans (Real.exp_le_exp.mpr hN)
    linarith only [hN']
  have hlw : ((windowBlocks a m J w).length+2:ℝ)≤Real.exp (Real.exp (((100:ℝ)^w/50)*Real.exp m)) := by
    have hh : (windowBlocks a m J w).length≤(commonBlocks a m W J).length := by
      obtain ⟨pre,he⟩ := windowBlocks_split a m J hw
      simp only [commonBlocks,he,List.length_append]; omega
    have harg : Real.exp (m:ℝ)≤Real.exp (((100:ℝ)^w/50)*Real.exp m) := by
      apply hlen.trans (Real.exp_le_exp.mpr _)
      nlinarith only [hpow,Real.exp_pos (m:ℝ)]
    exact (add_le_add (by exact_mod_cast hh : ((windowBlocks a m J w).length:ℝ)≤(commonBlocks a m W J).length) (le_refl (2:ℝ))) |>.trans (hl.trans (Real.exp_le_exp.mpr harg))
  have hNs : (windowSmoothing W m:ℝ)+1≤Real.exp ((20*(100:ℝ)^W+2)*((100:ℝ)^w*Real.exp m)) :=
    (windowSmoothing_bounds W m).2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hX (by positivity)))
  have hbLen : ((accurateBlock m (1/20)).length+2:ℝ)≤Real.exp ((100:ℝ)^w*Real.exp m) := by
    have hh : (accurateBlock m (1/20)).length≤(commonBlocks a m W J).length := by simp [commonBlocks]
    exact (add_le_add (by exact_mod_cast hh : ((accurateBlock m (1/20)).length:ℝ)≤(commonBlocks a m W J).length) (le_refl (2:ℝ))) |>.trans (hl.trans (Real.exp_le_exp.mpr hX))
  have hrLen : ((middleBlocks a m w J++accurateBlock m (1/20)).length+2:ℝ)≤Real.exp ((100:ℝ)^w*Real.exp m) := by
    have hh := middleBlocks_length_le (a := a) (m := m) J hw
    have hh' : (middleBlocks a m w J++accurateBlock m (1/20)).length≤(commonBlocks a m W J).length := by
      simp only [commonBlocks,List.length_append]; omega
    exact (add_le_add (by exact_mod_cast hh' : ((middleBlocks a m w J++accurateBlock m (1/20)).length:ℝ)≤(commonBlocks a m W J).length) (le_refl (2:ℝ))) |>.trans (hl.trans (Real.exp_le_exp.mpr hX))
  have hbOps : ∀ n∈accurateBlock m (1/20), (n:ℝ)≤Real.exp (Real.exp ((1/20)*((100:ℝ)^w*Real.exp m))) := by
    apply accurateBlock_bound (accurateGrid_le_one m)
    exact (mul_le_of_le_one_left (Real.exp_nonneg _) (accurateGrid_le_one m)).trans
      (Real.exp_le_exp.mpr (by linarith only [hX]))
  have hrOps : ∀ n∈middleBlocks a m w J++accurateBlock m (1/20), (n:ℝ)≤Real.exp (Real.exp ((1/4)*((100:ℝ)^w*Real.exp m))) := by
    intro n hn
    rcases List.mem_append.mp hn with hn|hn
    · rcases List.mem_append.mp hn with hn|hn
      · apply accurateBlock_bound (accurateGrid_le_one m) _ n hn
        simpa only [div_mul_eq_mul_div,mul_assoc,one_mul] using
          (mul_le_of_le_one_left (Real.exp_nonneg (((100:ℝ)^w/4)*Real.exp m)) (accurateGrid_le_one m))
      · exact (smaller_window_operations ha ha1 m w J (fun i hi => hJ i (hi.trans hw)) n hn).trans
          (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith only [show 0≤(100:ℝ)^w*Real.exp m by positivity] : ((100:ℝ)^w/50)*Real.exp m≤(1/4)*((100:ℝ)^w*Real.exp m))))
    · exact (hbOps n hn).trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith only [show 0≤(100:ℝ)^w*Real.exp m by positivity] : (1/20)*((100:ℝ)^w*Real.exp m)≤(1/4)*((100:ℝ)^w*Real.exp m))))
  exact ⟨hl,hNsmall,hlw,
    hbot _ _ (by have := windowSmoothing_pos W m; omega) hbLen hbOps hNs,
    hrest _ _ (by have := windowSmoothing_pos W m; omega) hrLen hrOps hNs⟩

lemma floor_size_lower {s : SplitSieve} {g U X : ℝ} {l : ℕ}
    (hX : 0<X) (hm : 0<s.meanLog) (hm' : s.meanLog≤2*X)
    (hscale : Real.exp (X/8)≤bandScale g U l) (hlarge : 4*X≤Real.exp (X/8)) :
    Real.exp (X/8)/(4*X)≤(bandSize s g U l:ℝ) := by
  have hf := Nat.lt_floor_add_one (bandScale g U l/s.meanLog)
  have hh := mul_lt_mul_of_pos_right hf hm
  rw [div_mul_cancel₀ _ hm.ne',add_mul,one_mul] at hh
  have hb := mul_le_mul_of_nonneg_left hm' (Nat.cast_nonneg (bandSize s g U l))
  change (bandScale g U l)<((bandSize s g U l:ℝ)*s.meanLog)+s.meanLog at hh
  apply (div_le_iff₀ (by positivity)).mpr
  linarith only [hf,hh,hb,hscale,hlarge,hm']

theorem eventually_window_bands {D a δ : ℝ} (hD : 1≤D) (ha : 0≤a) (ha1 : a≤1)
    (hδ : 0<δ) (W w : ℕ) (hw : w<W) :
    ∀ᶠ m : ℕ in atTop, ∀ J : ℕ → Finset ℕ,
      (∀ i<W, ∀ j∈J i, ((100:ℝ)^i*Real.exp m)≤j*Real.log 2 ∧
        j*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m) ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(PrimeLogMass.dyadicBatch j).card) →
      ∀ j∈J w,
        Nonempty (EntropyBand (dyadicSieve j) D (middleBlocks a m w J) 0
          (bandSize (dyadicSieve j) (accurateGrid m) (Real.exp (((100:ℝ)^w/4)*Real.exp m)) (accurateIterations m))
          (91*accurateGrid m)) ∧
        Nonempty (EntropyBand (dyadicSieve j) D (accurateBlock m (1/20)) (windowSmoothing W m)
          (bandSize (dyadicSieve j) (accurateGrid m) (Real.exp ((1/20)*Real.exp m)) (accurateIterations m))
          (91*accurateGrid m)) ∧
        Real.exp (((100:ℝ)^w*Real.exp m)/8)/(4*((100:ℝ)^w*Real.exp m))≤
          (bandSize (dyadicSieve j) (accurateGrid m) (Real.exp (((100:ℝ)^w/4)*Real.exp m)) (accurateIterations m):ℝ) := by
  have hwp := window_power_one w
  have hp : (0:ℝ)<100^w := by positivity
  have hmid := eventually_accurate_band (D := D) (A := (100:ℝ)^w) (B := 2*(100:ℝ)^w)
    (a := (100:ℝ)^w/4) (b := (100:ℝ)^w/50) hD hp (by positivity) (by linarith only [hp])
    (by linarith only [hp]) hδ
  have hbot := eventually_accurate_band (D := D) (A := 1) (B := 2*(100:ℝ)^w)
    (a := 1/20) (b := 1/100) hD (by norm_num) (by norm_num) (by norm_num) (by norm_num) hδ
  have hscale := eventually_accurate_scale (a := (100:ℝ)^w/4) (by positivity) 0
  have hlarge := eventually_mul_le_double_exp (a := (100:ℝ)^w/8) (by positivity) (4*(100:ℝ)^w)
  have hm2 := (windowScale_tendsto 0).eventually (eventually_ge_atTop (2:ℝ))
  filter_upwards [hmid,hbot,hscale,hlarge,eventually_window_tail_bounds hD ha ha1 W w hw,hm2]
    with m hmid hbot hscale hlarge htail hm2
  intro J hJ j hj
  simp only [pow_zero,one_mul] at hm2
  have hdata := hJ w hw j hj
  have hne := dyadic_dense_nonempty hδ hdata.2.2
  have hX2 : 2≤(100:ℝ)^w*Real.exp m := by nlinarith only [hm2,hwp]
  have hm := dyadic_mean_bounds hX2 hne hdata.1 hdata.2.1
  have hpj := dyadic_prime_bounds j
  have hdense : δ*(2:ℝ)^j/Real.log (2*(2:ℝ)^j)≤(dyadicSieve j).primes.card := by
    change δ*(2:ℝ)^j/Real.log (2*(2:ℝ)^j)≤(PrimeLogMass.dyadicBatch j).card
    simpa only [pow_succ,mul_comm] using hdata.2.2
  have hT : Real.exp ((100:ℝ)^w*Real.exp m)≤(2:ℝ)^j := by
    rw [←Real.exp_log (by positivity : (0:ℝ)<2^j),Real.log_pow]
    exact Real.exp_le_exp.mpr hdata.1
  have hThi : Real.log ((2:ℝ)^j)≤(2*(100:ℝ)^w)*Real.exp m := by
    rw [Real.log_pow]
    linarith only [hdata.2.1,hX2]
  obtain ⟨_,hN,hlen,_,_⟩ := htail J (fun i hi k hk => (hJ i hi k hk).2.1)
  have hmid' := hmid (dyadicSieve j) ((2:ℝ)^j) [] (windowBlocks a m J w) 0
    hne hpj hdense hT hThi
    (smaller_window_operations ha ha1 m w J (fun i hi k hk => (hJ i (hi.trans hw) k hk).2.1))
    (by simp only [Nat.cast_zero]; positivity) hlen
  have hTwo : (2:ℝ)≤Real.exp (Real.exp ((1/100)*Real.exp m)) := by
    have he : 1≤Real.exp ((1/100)*Real.exp (m:ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
    linarith only [Real.add_one_le_exp (Real.exp ((1/100)*Real.exp (m:ℝ))),he]
  have hbot' := hbot (dyadicSieve j) ((2:ℝ)^j) [] [] (windowSmoothing W m)
    hne hpj hdense
    ((Real.exp_le_exp.mpr (by nlinarith only [hwp,Real.exp_pos (m:ℝ)] : 1*Real.exp m≤(100:ℝ)^w*Real.exp m)).trans hT)
    hThi (by simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true]) hN
    (by simpa only [List.length_nil,Nat.cast_zero,zero_add] using hTwo)
  refine ⟨?_,?_,?_⟩
  · simpa only [List.nil_append,accurateBlock,middleBlocks] using hmid'
  · simpa only [List.nil_append,List.append_nil,accurateBlock] using hbot'
  · apply floor_size_lower (by linarith only [hX2]) (by linarith only [hm.1]) hm.2
    · simpa only [pow_zero,one_mul,div_div,show (4:ℝ)*2=8 by norm_num,div_mul_eq_mul_div] using hscale
    · simpa only [mul_assoc,div_mul_eq_mul_div] using hlarge

end GaussianMoat

end OAI
end
end

section
section
namespace OAI

namespace GaussianMoat
open scoped BigOperators Classical
open Filter

lemma eventually_length_smoothing :
    ∀ᶠ X : ℝ in atTop, ∀ p L N : ℝ,
      0<p → p≤2*Real.exp (21/20*X) → 0≤L → L≤Real.exp (21/50*X) →
      Real.exp (20*X)≤N → L≤N ∧ L/(N+1)≤((1/4)/p)/2 := by
  have hh := eventually_mul_exp_le_exp (a := 147/100) (b := 20) (by norm_num) 16
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with X hh hX
  intro p L N hp hp' hL hL' hN
  have hNpos : 0<N+1 := by linarith only [hN,Real.exp_pos (20*X)]
  have hm := mul_le_mul hp' hL' hL (by positivity : 0≤2*Real.exp (21/20*X))
  rw [mul_assoc,←Real.exp_add,show 21/20*X+21/50*X=147/100*X by ring] at hm
  refine ⟨hL'.trans ((Real.exp_le_exp.mpr (by linarith only [hX])).trans hN),?_⟩
  apply (div_le_iff₀ hNpos).mpr
  have he : ((1/4:ℝ)/p)/2=(1/8)/p := by ring
  rw [he]
  apply (mul_le_mul_iff_left₀ hp).mp
  have heq : (1/8/p)*(N+1)*p=(N+1)/8 := by field_simp
  rw [heq]
  linarith only [hm,hh,hN]

theorem eventually_window_batch {D a δ : ℝ} {K : ℕ}
    (hD : 1≤D) (ha : 0<a) (ha1 : a≤1) (haδ : 2*a≤δ)
    (hgap : a≤(2:ℝ)^K*topCoefficient a) (W w : ℕ) (hw : w<W) :
    ∀ᶠ m : ℕ in atTop, ∀ J : ℕ → Finset ℕ,
      (∀ i<W, ∀ j∈J i, ((100:ℝ)^i*Real.exp m)≤j*Real.log 2 ∧
        j*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m) ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(PrimeLogMass.dyadicBatch j).card) →
      (∀ i∈J w, ∀ j∈J w, i<j → i+K≤j) →
      ∀ j∈J w, ∀ E : ℝ, E≤(topCoefficient a/4)*(2:ℝ)^j/10000 →
        Nonempty (BatchCertificate D (commonBlocks a m W J) (windowSmoothing W m)
          (dyadicSieve j) (batchWordLength j) E
          ((topCoefficient a/4)/(10000000*Real.log ((2:ℝ)^j)))) := by
  have hδ : 0<δ := by linarith only [ha,haδ]
  have hc : 0<topCoefficient a/4 := by exact div_pos (topCoefficient_pos ha) (by norm_num)
  have ht := windowScale_tendsto w
  have hε : 0 < min (1/1024:ℝ) (Real.exp (-100)/(512*640000)) := by positivity
  have herr := eventually_accurate_error (2*(100:ℝ)^w) hε
  filter_upwards [eventually_window_bands hD ha.le ha1 hδ W w hw,
    eventually_window_tail_bounds hD ha.le ha1 W w hw,
    ht.eventually (eventually_window_top hD ha haδ hgap),
    ht.eventually (eventually_integer_batch_bounds hD),
    ht.eventually eventually_coverage_hazard,ht.eventually eventually_coverage_data_cost,
    ht.eventually (eventually_package_displacement hc),
    ht.eventually eventually_length_smoothing,herr,ht.eventually (eventually_ge_atTop (1600:ℝ))]
    with m hbands htail htop hint hhazard hccost hpcost hsmooth herr hX
  intro J hJ hsep j hj E hE
  let X : ℝ := (100:ℝ)^w*Real.exp m
  let s := dyadicSieve j
  have hdata := hJ w hw j hj
  have hne : s.primes.Nonempty := dyadic_dense_nonempty hδ hdata.2.2
  have hpj := dyadic_prime_bounds j
  have hm := dyadic_mean_bounds (by linarith only [hX]) hne hdata.1 hdata.2.1
  have hTpos : (0:ℝ)<2^j := by positivity
  have hT : Real.exp X≤(2:ℝ)^j := by
    rw [←Real.exp_log hTpos,Real.log_pow]
    exact Real.exp_le_exp.mpr hdata.1
  have hprime : ∀ i : s.SignedIndex, Real.exp X≤(s.signedPrime i:ℝ) ∧
      (s.signedPrime i:ℝ)≤2*Real.exp (21/20*X) := by
    intro i
    have hp := hpj _ (s.enumeration i.2).property
    refine ⟨hT.trans hp.1,hp.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [←Real.exp_log hTpos,Real.log_pow]
    exact Real.exp_le_exp.mpr hdata.2.1
  obtain ⟨pre,hpre⟩ := windowBlocks_split a m J hw
  obtain ⟨hband,hbsize⟩ := htop (J w) pre hsep (hJ w hw) j hj
  obtain ⟨qtop⟩ := hband
  obtain ⟨hmid,hbot,hbmid⟩ := hbands J hJ j hj
  obtain ⟨qmid⟩ := hmid
  obtain ⟨qbot⟩ := hbot
  obtain ⟨_,_,_,hbotcost,hrestcost⟩ := htail J (fun i hi k hk => (hJ i hi k hk).2.1)
  have herrors : (91*accurateGrid m)*s.meanLog≤ min (1/1024:ℝ) (Real.exp (-100)/(512*640000)) := by
    have hh := mul_le_mul_of_nonneg_left hm.2 (by have := accurateGrid_pos m; positivity : 0≤91*accurateGrid m)
    exact hh.trans (by simpa only [mul_assoc] using herr)
  have hcoverage := coverage_from_scalar_guards s D X (windowSmoothing W m)
    (middleBlocks a m w J) (accurateBlock m (1/20)) _ _ _ qmid qbot
    (by linarith only [hm.1]) (by have := windowSmoothing_pos W m; omega)
    (by linarith only [hX]) hprime
    (herrors.trans (min_le_right _ _)) (herrors.trans (min_le_left _ _))
    (hccost _ _ hbotcost hbmid) (fun i => hhazard _ ((Real.exp_pos X).trans_le (hprime i).1) (hprime i).2)
  obtain ⟨hn,hshort,hnL,hnL',hnmax,hLmax⟩ := hint j hdata.1 hdata.2.1
  have hN : Real.exp (20*X)≤(windowSmoothing W m:ℝ) := by
    apply le_trans _ (windowSmoothing_bounds W m).1
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤100) hw.le) (Real.exp_nonneg (m:ℝ))
    dsimp only [X]
    linarith only [hh]
  have hNLength : batchWordLength j≤windowSmoothing W m := by
    have h := hsmooth ((2:ℝ)^j) (batchWordLength j) (windowSmoothing W m) hTpos
      (by
        have hh : (2:ℝ)^j≤Real.exp (21/20*X) := by
          rw [←Real.exp_log hTpos,Real.log_pow]
          exact Real.exp_le_exp.mpr hdata.2.1
        linarith only [hh,Real.exp_nonneg (21/20*X)])
      (Nat.cast_nonneg _) hLmax hN
    exact_mod_cast h.1
  refine ⟨{
    pre := pre++topBlocks a (J w)
    rest := middleBlocks a m w J++accurateBlock m (1/20)
    schedule := by simp only [commonBlocks,middleBlocks,hpre,List.append_assoc]
    T := (2:ℝ)^j
    nonempty := hne
    prime_scale := hpj
    large := by linarith only [hT,Real.add_one_le_exp X,hX]
    mean := hm.1
    b := bandSize s topParameter (a*(2:ℝ)^j) topIterations
    n := packageRepetitions j
    τ := 1/4
    A := X/400
    η := 1/100
    δ := 1/10000
    u := fun i => (s.signedPrime i:ℝ)*Real.exp (-X/200)
    band := qtop
    coverage := hcoverage
    cap := qtop.size_cap (by linarith only [hm.1])
    repetitions := hn
    length := batchWordLength_pos j
    floor := by norm_num
    gain := by linarith only [hX]
    exceptions := fun i => by positivity
    short := fun i => hshort.trans_le (hpj _ (s.enumeration i.2).property).1
    smooth_length := hNLength
    smooth_error := fun i => (hsmooth _ _ _ ((Real.exp_pos X).trans_le (hprime i).1)
      (hprime i).2 (Nat.cast_nonneg _) hLmax hN).2
    list := ?_
    rate := ?_
  }⟩
  · intro i
    have hh := package_list_arithmetic hX hT ((Real.exp_pos X).trans_le (hprime i).1)
      (hpj _ (s.enumeration i.2).property).2 hnL
    dsimp only [s] at hh
    convert hh using 1; congr 2; ring_nf
  · apply package_rate_arithmetic (by linarith only [hX]) hTpos hc
      (by simpa only [Real.log_pow] using hdata.1)
      (by simpa only [Real.log_pow] using hdata.2.1) hm.2
      (by convert hbsize using 1; ring) hnL'
      (hpcost _ _ _ (Nat.cast_nonneg _) hnmax hrestcost hT) hE

end GaussianMoat

end OAI
end
end

section
section
namespace OAI

namespace GaussianMoat

section
open scoped BigOperators Classical

noncomputable def binEnum (J : Finset ℕ) (n : ℕ) : ℕ :=
  if h : n<J.card then J.orderEmbOfFin rfl ⟨n,h⟩ else 0

lemma binEnum_eq (J : Finset ℕ) {n : ℕ} (hn : n<J.card) :
    binEnum J n=J.orderEmbOfFin rfl ⟨n,hn⟩ := by simp only [binEnum,dite_eq_left hn]

lemma binEnum_mem (J : Finset ℕ) {n : ℕ} (hn : n<J.card) : binEnum J n∈J := by
  rw [binEnum_eq J hn]
  exact J.orderEmbOfFin_mem rfl _

lemma binEnum_strictMono (J : Finset ℕ) {n k : ℕ} (hnk : n<k) (hk : k<J.card) :
    binEnum J n<binEnum J k := by
  rw [binEnum_eq J (hnk.trans hk),binEnum_eq J hk]
  exact (J.orderEmbOfFin rfl).strictMono hnk

lemma binEnum_surj (J : Finset ℕ) {j : ℕ} (hj : j∈J) :
    ∃ n<J.card, binEnum J n=j := by
  have hh : j∈Set.range (J.orderEmbOfFin rfl) := by rw [J.range_orderEmbOfFin rfl]; exact hj
  obtain ⟨i,hi⟩ := hh
  exact ⟨i.val,i.isLt,(binEnum_eq J i.isLt).trans hi⟩

lemma binEnum_sum (J : Finset ℕ) (f : ℕ → ℝ) :
    (∑ n∈Finset.range J.card, f (binEnum J n))=∑ j∈J, f j := by
  apply Finset.sum_bij (fun n _ => binEnum J n)
  · intro n hn; exact binEnum_mem J (Finset.mem_range.mp hn)
  · intro n hn k hk he
    have hn' := Finset.mem_range.mp hn
    have hk' := Finset.mem_range.mp hk
    rcases lt_trichotomy n k with h|h|h
    · exact (ne_of_lt (binEnum_strictMono J h hk') he).elim
    · exact h
    · exact (ne_of_lt (binEnum_strictMono J h hn') he.symm).elim
  · intro j hj
    obtain ⟨n,hn,he⟩ := binEnum_surj J hj
    exact ⟨n,Finset.mem_range.mpr hn,he⟩
  · intro n hn; rfl

lemma precedingFactors_enum_subset (J : Finset ℕ) {n : ℕ} (hn : n<J.card) :
    precedingFactors (fun k => dyadicSieve (binEnum J k)) n⊆
      (J.filter (·<binEnum J n)).biUnion (fun j => (dyadicSieve j).availableFactors) := by
  intro f hf
  obtain ⟨k,hk,hf⟩ := Finset.mem_biUnion.mp hf
  have hk' := Finset.mem_range.mp hk
  apply Finset.mem_biUnion.mpr
  exact ⟨binEnum J k,Finset.mem_filter.mpr ⟨binEnum_mem J (hk'.trans hn),binEnum_strictMono J hk' hn⟩,hf⟩

lemma precedingFactors_enum_cost (J : Finset ℕ) {K n : ℕ} (hK : 0<K) (hn : n<J.card)
    (hsep : ∀ a∈J, ∀ b∈J, a<b → a+K≤b) :
    residueWeight (precedingFactors (fun k => dyadicSieve (binEnum J k)) n)≤
      (4*Real.log 4/((2:ℝ)^K-1))*(2:ℝ)^(binEnum J n) := by
  apply (residueWeight_mono (precedingFactors_enum_subset J hn)).trans
  apply separated_factor_cost _ hK
  · intro a ha b hb hab
    exact hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
  · intro a ha
    exact hsep a (Finset.mem_filter.mp ha).1 (binEnum J n) (binEnum_mem J hn) (Finset.mem_filter.mp ha).2

lemma precedingFactors_enum_all (J : Finset ℕ) :
    precedingFactors (fun k => dyadicSieve (binEnum J k)) J.card=
      J.biUnion (fun j => (dyadicSieve j).availableFactors) := by
  ext f
  constructor
  · intro hf
    obtain ⟨k,hk,hf⟩ := Finset.mem_biUnion.mp hf
    exact Finset.mem_biUnion.mpr ⟨binEnum J k,binEnum_mem J (Finset.mem_range.mp hk),hf⟩
  · intro hf
    obtain ⟨j,hj,hf⟩ := Finset.mem_biUnion.mp hf
    obtain ⟨n,hn,he⟩ := binEnum_surj J hj
    exact Finset.mem_biUnion.mpr ⟨n,Finset.mem_range.mpr hn,by simpa only [he] using hf⟩

open scoped BigOperators Classical
open Filter

noncomputable def allBins (W : ℕ) (J : ℕ → Finset ℕ) : Finset ℕ :=
  (Finset.range W).biUnion J

lemma bin_window_gap {X : ℝ} {K u v i j : ℕ} (hX : 0<X)
    (hK : K*Real.log 2≤X) (huv : u<v)
    (hi : i*Real.log 2≤21/20*((100:ℝ)^u*X))
    (hj : (100:ℝ)^v*X≤j*Real.log 2) : i+K≤j := by
  have hp := mul_le_mul_of_nonneg_right (window_power_step huv) hX.le
  have ho := window_power_one u
  have hu : X≤(100:ℝ)^u*X := by nlinarith only [ho,hX]
  have hh : ((i+K:ℕ):ℝ)*Real.log 2≤(j:ℝ)*Real.log 2 := by
    push_cast
    linarith only [hp,hu,hK,hi,hj,hX]
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hn : (i+K:ℕ)≤(j:ℝ) := (mul_le_mul_iff_left₀ hl).mp hh
  exact_mod_cast hn

lemma allBins_separated {X : ℝ} {K W : ℕ} (J : ℕ → Finset ℕ) (hX : 0<X)
    (hK : K*Real.log 2≤X)
    (hb : ∀ w<W, ∀ j∈J w, (100:ℝ)^w*X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*((100:ℝ)^w*X))
    (hsep : ∀ w<W, ∀ i∈J w, ∀ j∈J w, i<j → i+K≤j) :
    ∀ i∈allBins W J, ∀ j∈allBins W J, i<j → i+K≤j := by
  intro i hi j hj hij
  obtain ⟨u,hu,hi⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨v,hv,hj⟩ := Finset.mem_biUnion.mp hj
  have hu' := Finset.mem_range.mp hu
  have hv' := Finset.mem_range.mp hv
  rcases lt_trichotomy u v with huv|rfl|hvu
  · exact bin_window_gap hX hK huv (hb u hu' i hi).2 (hb v hv' j hj).1
  · exact hsep u hu' i hi j hj hij
  · have hh := bin_window_gap hX hK hvu (hb v hv' j hj).2 (hb u hu' i hi).1
    omega

lemma bins_disjoint {X : ℝ} {W : ℕ} (J : ℕ → Finset ℕ) (hX : 0<X)
    (hb : ∀ w<W, ∀ j∈J w, (100:ℝ)^w*X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*((100:ℝ)^w*X)) :
    (↑(Finset.range W) : Set ℕ).PairwiseDisjoint J := by
  intro u hu v hv hne
  apply Finset.disjoint_left.mpr
  intro j hju hjv
  have hp (i k : ℕ) (hik : i<k) (hji : j∈J i) (hjk : j∈J k) (hi : i<W) (hk : k<W) : False := by
    have hh := mul_le_mul_of_nonneg_right (window_power_step hik) hX.le
    have hlo := (hb k hk j hjk).1
    have hhi := (hb i hi j hji).2
    have hz : 0<(100:ℝ)^k*X := by positivity
    linarith only [hh,hlo,hhi,hz]
  rcases lt_or_gt_of_ne hne with h|h
  · exact hp u v h hju hjv (Finset.mem_range.mp hu) (Finset.mem_range.mp hv)
  · exact hp v u h hjv hju (Finset.mem_range.mp hv) (Finset.mem_range.mp hu)

lemma allBins_card_upper {m W : ℕ} (J : ℕ → Finset ℕ) (hm : 2≤Real.exp m)
    (hb : ∀ w<W, ∀ j∈J w, j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) :
    ((allBins W J).card:ℝ)≤3*(W:ℝ)*(100:ℝ)^W*Real.exp m := by
  have hh := Finset.card_biUnion_le (s := Finset.range W) (t := J)
  have hs : (∑ w∈Finset.range W, ((J w).card:ℝ))≤(W:ℝ)*(3*(100:ℝ)^W*Real.exp m) := by
    calc
      _ ≤ ∑ w∈Finset.range W, 3*(100:ℝ)^W*Real.exp m := by
        apply Finset.sum_le_sum
        intro w hw
        have hw' := Finset.mem_range.mp hw
        have hp := window_power_one w
        have he : 2≤(100:ℝ)^w*Real.exp m := by nlinarith only [hp,hm]
        have hc := narrow_bins_card he (J w) (hb w hw')
        have hp' := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤100) hw'.le) (Real.exp_nonneg (m:ℝ))
        linarith only [hc,hp']
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hh' : ((allBins W J).card:ℝ)≤∑ w∈Finset.range W, ((J w).card:ℝ) := by exact_mod_cast hh
  linarith only [hh',hs]

lemma allBins_rate {X c t : ℝ} {W : ℕ} (J : ℕ → Finset ℕ) (hX : 0<X) (hc : 0<c)
    (hb : ∀ w<W, ∀ j∈J w, (100:ℝ)^w*X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*((100:ℝ)^w*X))
    (hdense : ∀ w<W, t*((100:ℝ)^w*X)≤(J w).card) :
    (W:ℝ)*(c*t/10500000)≤∑ j∈allBins W J, c/(10000000*Real.log ((2:ℝ)^j)) := by
  rw [allBins,Finset.sum_biUnion (bins_disjoint J hX hb)]
  have hs : ∀ w<W, c*t/10500000≤∑ j∈J w, c/(10000000*Real.log ((2:ℝ)^j)) := by
    intro w hw
    have hwX : 0<(100:ℝ)^w*X := by positivity
    have hl : ∀ j∈J w, 0<Real.log ((2:ℝ)^j) := by
      intro j hj; rw [Real.log_pow]; exact hwX.trans_le (hb w hw j hj).1
    have ht' := hdense w hw
    have hh : (J w).card*(c/(10500000*((100:ℝ)^w*X)))≤∑ j∈J w, c/(10000000*Real.log ((2:ℝ)^j)) := by
      calc
        _ = ∑ _j∈J w, c/(10500000*((100:ℝ)^w*X)) := by simp only [Finset.sum_const,nsmul_eq_mul]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j hj
          apply div_le_div_of_nonneg_left hc.le (by have := hl j hj; positivity : 0<10000000*Real.log ((2:ℝ)^j))
          rw [Real.log_pow]
          linarith only [(hb w hw j hj).2]
    have hm := mul_le_mul_of_nonneg_right ht' (show 0≤c/(10500000*((100:ℝ)^w*X)) by positivity)
    have he : t*((100:ℝ)^w*X)*(c/(10500000*((100:ℝ)^w*X)))=c*t/10500000 := by field_simp
    rw [he] at hm
    exact hm.trans hh
  have hh := Finset.sum_le_sum (s := Finset.range W) (fun w hw => hs w (Finset.mem_range.mp hw))
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using hh

end

open scoped BigOperators Classical
open Filter

lemma exists_separated_parameters : ∃ a δ t : ℝ, ∃ K : ℕ,
    0<a ∧ a≤1 ∧ 2*a≤δ ∧ 0<t ∧ 0<K ∧
    a≤(2:ℝ)^K*topCoefficient a ∧
    4*Real.log 4/((2:ℝ)^K-1)≤(topCoefficient a/4)/10000 ∧
    ∀ᶠ X : ℝ in atTop, ∃ J : Finset ℕ,
      t*X≤J.card ∧ (∀ i∈J, ∀ j∈J, i<j → i+K≤j) ∧
      ∀ j∈J, X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*X ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(PrimeLogMass.dyadicBatch j).card := by
  obtain ⟨c,δ,hc,hδ,he⟩ := PrimeLogMass.eventually_dense_split_bins
  let a := min (δ/4) 1
  have ha : 0<a := lt_min (by positivity) (by norm_num)
  have ha1 : a≤1 := min_le_right _ _
  have haδ : 2*a≤δ := by have := min_le_left (δ/4) 1; dsimp only [a]; linarith only [this,hδ]
  have hv : 0<topCoefficient a := topCoefficient_pos ha
  have powtop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)
  have hn := powtop.eventually (eventually_ge_atTop (max (a/topCoefficient a) (1+160000*Real.log 4/topCoefficient a)))
  obtain ⟨K,hK,hpow⟩ := (eventually_gt_atTop 0 |>.and hn).exists
  have hlo := (le_max_left _ _).trans hpow
  have hhi := (le_max_right _ _).trans hpow
  have hgap : a≤(2:ℝ)^K*topCoefficient a := (div_le_iff₀ hv).mp hlo
  have hden : 0<(2:ℝ)^K-1 := by
    have := one_lt_pow₀ (by norm_num : (1:ℝ)<2) (by omega : K≠0)
    linarith only [this]
  have hcost : 4*Real.log 4/((2:ℝ)^K-1)≤(topCoefficient a/4)/10000 := by
    have hh : 160000*Real.log 4≤((2:ℝ)^K-1)*topCoefficient a := by
      apply (div_le_iff₀ hv).mp
      linarith only [hhi]
    apply (div_le_iff₀ hden).mpr
    linarith only [hh]
  refine ⟨a,δ,c/K,K,ha,ha1,haδ,div_pos hc (by exact_mod_cast hK),hK,hgap,hcost,?_⟩
  filter_upwards [he] with X hX
  obtain ⟨J,hJ,hp⟩ := hX
  obtain ⟨b,_,hcard,hsep⟩ := thin_bins J hK
  refine ⟨J.filter (fun j => j%K=b),?_,hsep,?_⟩
  · have hh := (div_le_div_of_nonneg_right hJ (Nat.cast_nonneg K)).trans hcard
    simpa only [div_mul_eq_mul_div] using hh
  · intro j hj
    exact hp j (Finset.mem_filter.mp hj).1

end GaussianMoat

end OAI
end
end

section
section
namespace OAI

namespace GaussianMoat
open scoped BigOperators Classical
open Filter

lemma allBins_scale_bound {m W : ℕ} (J : ℕ → Finset ℕ)
    (hb : ∀ w<W, ∀ j∈J w, j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m))
    {j : ℕ} (hj : j∈allBins W J) :
    (2:ℝ)^j≤Real.exp (21/20*(100:ℝ)^W*Real.exp m) := by
  obtain ⟨w,hw,hj⟩ := Finset.mem_biUnion.mp hj
  have hw' := Finset.mem_range.mp hw
  have hp := mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤100) hw'.le) (Real.exp_nonneg (m:ℝ))
  rw [←Real.exp_log (by positivity : (0:ℝ)<2^j),Real.log_pow]
  apply Real.exp_le_exp.mpr
  linarith only [hb w hw' j hj,hp]

lemma eventually_allBins_weight (W : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ J : ℕ → Finset ℕ,
      (∀ w<W, ∀ j∈J w, j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) →
      residueWeight ((allBins W J).biUnion (fun j => (dyadicSieve j).availableFactors))≤
        Real.exp ((2*(100:ℝ)^W)*Real.exp m) := by
  have hp := eventually_poly_le_exp_linear (4*Real.log 4*(3*(W:ℝ)*(100:ℝ)^W))
    (a := (19/20)*(100:ℝ)^W) (by positivity) 1
  have ht : Tendsto (fun m : ℕ => Real.exp (m:ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually hp,ht.eventually (eventually_ge_atTop (2:ℝ))] with m hp hm
  intro J hJ
  have he := fun (j : ℕ) (hj : j∈allBins W J) => allBins_scale_bound J hJ hj
  have hcard := allBins_card_upper J hm hJ
  have hs : (∑ j∈allBins W J, residueWeight (dyadicSieve j).availableFactors)≤
      (4*Real.log 4)*((allBins W J).card:ℝ)*Real.exp (21/20*(100:ℝ)^W*Real.exp m) := by
    calc
      _ ≤ ∑ _j∈allBins W J, (4*Real.log 4)*Real.exp (21/20*(100:ℝ)^W*Real.exp m) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (dyadicSieve_available_weight j).trans
          (mul_le_mul_of_nonneg_left (he j hj) (by positivity))
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hcard' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcard (show 0≤4*Real.log 4 by positivity))
    (Real.exp_nonneg (21/20*(100:ℝ)^W*Real.exp m))
  have hh := mul_le_mul_of_nonneg_right hp (Real.exp_nonneg (21/20*(100:ℝ)^W*Real.exp m))
  rw [←Real.exp_add] at hh
  simp only [pow_one] at hh
  have heq : (19/20)*100^W*Real.exp (m:ℝ)+21/20*100^W*Real.exp m=
      (2*(100:ℝ)^W)*Real.exp m := by ring
  rw [heq] at hh
  apply (residueWeight_biUnion_le _ _).trans (hs.trans (hcard'.trans _))
  convert hh using 1; ring

theorem eventually_allBins_smoothing (D : ℝ) (W : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ J : ℕ → Finset ℕ,
      (∀ w<W, ∀ j∈J w, j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) →
      (∀ i∈allBins W J, ∀ j∈allBins W J, ∀ a<batchWordLength j,
        2*Real.binEntropy ((a:ℝ)/(windowSmoothing W m+1))+
          ((a:ℝ)/(windowSmoothing W m+1))*((batchWordLength i:ℝ)*Real.log (latticeBall D).card+
            2*residueWeight ((allBins W J).biUnion (fun j => (dyadicSieve j).availableFactors)))≤
          Real.exp (-Real.exp m)) ∧
      ((allBins W J).card:ℝ)*Real.exp (-Real.exp m)≤1 := by
  have hA : 1≤2*(100:ℝ)^W := by have := window_power_one W; linarith only [this]
  have ht : Tendsto (fun m : ℕ => Real.exp (m:ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_allBins_weight W,
    ht.eventually (eventually_smoothing_guard (H := Real.log (latticeBall D).card) hA),
    ht.eventually (eventually_smoothing_total (3*(W:ℝ)*(100:ℝ)^W)),
    ht.eventually (eventually_ge_atTop (2:ℝ))] with m hweight hsmooth htotal hm
  intro J hJ
  have hL (j : ℕ) (hj : j∈allBins W J) :
      (batchWordLength j:ℝ)≤Real.exp ((2*(100:ℝ)^W)*Real.exp m) := by
    apply (batchWordLength_le_scale j).trans ((allBins_scale_bound J hJ hj).trans _)
    apply Real.exp_le_exp.mpr
    have : 0≤(100:ℝ)^W*Real.exp m := by positivity
    linarith only [this]
  constructor
  · intro i hi j hj a ha
    apply hsmooth _ _ _ _ (Nat.cast_nonneg _)
      ((show (a:ℝ)≤batchWordLength j by exact_mod_cast ha.le).trans (hL j hj))
      (Nat.cast_nonneg _) (hL i hi) (hweight J hJ)
    convert (windowSmoothing_bounds W m).1 using 1
    congr 1
    ring
  · exact (mul_le_mul_of_nonneg_right (allBins_card_upper J hm hJ)
      (Real.exp_nonneg _)).trans htotal

end GaussianMoat

end OAI
end
end

section
section
namespace OAI

namespace GaussianMoat
open scoped BigOperators Classical
open Filter

theorem exists_sieveCertificate (D : ℝ) (hD : 1≤D) : Nonempty (SieveCertificate D) := by
  obtain ⟨a,δ,t,K,ha,ha1,haδ,ht,hK,hgap,hcost,hdensity⟩ := exists_separated_parameters
  let c := topCoefficient a/4
  have hc : 0<c := div_pos (topCoefficient_pos ha) (by norm_num)
  let rate := c*t/10500000
  have hrate : 0<rate := by dsimp only [rate]; positivity
  obtain ⟨W,hW⟩ := exists_nat_gt (max 0 ((Real.log (latticeBall D).card+1)/rate))
  have hW0 : 0<W := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hW)
  have hWrate : Real.log (latticeBall D).card+1<(W:ℝ)*rate :=
    (div_lt_iff₀ hrate).mp ((le_max_right _ _).trans_lt hW)
  have hbatch : ∀ᶠ m : ℕ in atTop, ∀ w∈Finset.range W, ∀ J : ℕ → Finset ℕ,
      (∀ i<W, ∀ j∈J i, ((100:ℝ)^i*Real.exp m)≤j*Real.log 2 ∧
        j*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m) ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(PrimeLogMass.dyadicBatch j).card) →
      (∀ i∈J w, ∀ j∈J w, i<j → i+K≤j) →
      ∀ j∈J w, ∀ E : ℝ, E≤c*(2:ℝ)^j/10000 →
        Nonempty (BatchCertificate D (commonBlocks a m W J) (windowSmoothing W m)
          (dyadicSieve j) (batchWordLength j) E (c/(10000000*Real.log ((2:ℝ)^j)))) := by
    apply (Finset.eventually_all (Finset.range W)).mpr
    intro w hw
    exact eventually_window_batch hD ha ha1 haδ hgap W w (Finset.mem_range.mp hw)
  obtain ⟨X0,hX0⟩ := eventually_atTop.mp hdensity
  have hexp : Tendsto (fun m : ℕ => Real.exp (m:ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨m,hbatch,hsmooth,hm⟩ :=
    (hbatch.and ((eventually_allBins_smoothing D W).and
      (hexp.eventually (eventually_ge_atTop (max X0 (K*Real.log 2)))))).exists
  have hmX : X0≤Real.exp (m:ℝ) := (le_max_left _ _).trans hm
  have hmK : K*Real.log 2≤Real.exp (m:ℝ) := (le_max_right _ _).trans hm
  have hbexists : ∀ w : ℕ, ∃ J : Finset ℕ,
      t*((100:ℝ)^w*Real.exp m)≤J.card ∧
      (∀ i∈J, ∀ j∈J, i<j → i+K≤j) ∧
      ∀ j∈J, (100:ℝ)^w*Real.exp m≤j*Real.log 2 ∧
        j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m) ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(PrimeLogMass.dyadicBatch j).card := by
    intro w
    apply hX0 _ (hmX.trans _)
    have := window_power_one w
    nlinarith only [this,Real.exp_pos (m:ℝ)]
  choose J hdense hsep hbounds using hbexists
  let U := allBins W J
  have hJ : ∀ w<W, ∀ j∈J w, (100:ℝ)^w*Real.exp m≤j*Real.log 2 ∧
      j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m) := by
    intro w _ j hj; exact ⟨(hbounds w j hj).1,(hbounds w j hj).2.1⟩
  have hU : U.Nonempty := by
    have hCard0 : 0<(J 0).card := by
      have hpos : 0<t*((100:ℝ)^0*Real.exp m) := by positivity
      exact_mod_cast hpos.trans_le (hdense 0)
    obtain ⟨j,hj⟩ := Finset.card_pos.mp hCard0
    exact ⟨j,Finset.mem_biUnion.mpr ⟨0,Finset.mem_range.mpr hW0,hj⟩⟩
  have hUcard : 0<U.card := Finset.card_pos.mpr hU
  have hUlast : U.card-1+1=U.card := by omega
  have hUsep := allBins_separated J (Real.exp_pos (m:ℝ)) hmK hJ (fun w _ => hsep w)
  obtain ⟨hsmooth,htotal⟩ := hsmooth J (fun w hw j hj => (hJ w hw j hj).2)
  refine ⟨{
    schedule := commonBlocks a m W J
    smoothing := windowSmoothing W m
    batches := binEnum U
    last := U.card-1
    lengths := fun n => batchWordLength (binEnum U n)
    rates := fun n => c/(10000000*Real.log ((2:ℝ)^(binEnum U n)))
    error := Real.exp (-Real.exp m)
    batch := ?_
    divides := ?_
    nonneg := (Real.exp_pos _).le
    smooth := ?_
    excess := ?_
  }⟩
  · intro n hn
    apply Classical.choice
    have hn' : n<U.card := by omega
    have hmem := binEnum_mem U hn'
    obtain ⟨w,hw,hjw⟩ := Finset.mem_biUnion.mp hmem
    apply (hbatch w hw J (fun w _ => hbounds w) (hsep w) _ hjw _)
    have hh := precedingFactors_enum_cost U hK hn' hUsep
    have hm := mul_le_mul_of_nonneg_right hcost (show (0:ℝ)≤2^(binEnum U n) by positivity)
    exact hh.trans (by convert hm using 1; ring)
  · intro n hn
    exact batchWordLength_dvd (binEnum_strictMono U (Nat.lt_succ_self n) (by omega)).le
  · intro n hn a ha'
    rw [hUlast,precedingFactors_enum_all]
    exact hsmooth _ (binEnum_mem U (by omega)) _ (binEnum_mem U (by omega)) a ha'
  · rw [hUlast,binEnum_sum U (fun j => c/(10000000*Real.log ((2:ℝ)^j)))]
    have hsum := allBins_rate J (Real.exp_pos (m:ℝ)) hc hJ (fun w _ => hdense w)
    have hcost' : ((U.card-1:ℕ):ℝ)*Real.exp (-Real.exp m)≤1 :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le U.card 1 : ((U.card-1:ℕ):ℝ)≤U.card)
        (Real.exp_nonneg _)).trans htotal
    have hh := hWrate.trans_le hsum
    linarith only [hcost',hh]

theorem finiteSieveEndpoint_proved : FiniteSieveEndpoint :=
  finiteSieve_of_certificates exists_sieveCertificate

theorem fullMain_oai : MainEndpoint ∧ UniformEndpoint :=
  endpoints_of_finiteSieve finiteSieveEndpoint_proved

end GaussianMoat

end OAI
end
end

theorem solution : type_of% @OAI.GaussianMoat.fullMain_oai := @OAI.GaussianMoat.fullMain_oai
