-- Prove2me | solution 1 for LodhaMoore.phi_cons_and_eq_phi_of_cons_and_Phi_fibers
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:34:28.665776+00:00
-- url     : https://prove2.me/submissions/ad7c966d-c27a-4154-bc27-317542fa1a44

import Mathlib
import Definitions.Def_LodhaMoore
import Definitions.Def_Monod_PiecewiseProjective
import Definitions.Def_Chou_Classes
import Definitions.Def_Garrido_Amenability
section
/-! Development: `a`, `b`, `c` are the homeomorphisms the bundle names (`ofReal` returns the
extension of `aFun`, `bFun`, `cFun`), and their values on `ℝ`. -/

namespace LodhaMoore

end LodhaMoore
end

section
/-! Shared definitions for the Carrière–Ghys argument (Monod C9, `not_isAmenableRel_mob`). -/

namespace Monod.Dev.CG

open Matrix

variable {A : Subring ℝ}

end Monod.Dev.CG
end

section
/-! A4 of the Carrière–Ghys argument: for `|t| < 2`, the elliptic Möbius map `a_t : x ↦ t - 1/x`
preserves the finite measure `dx / (x² - t x + 1)` on `P¹`, which has the same null sets as
`volP1`; so `a_t` is conservative and every a.e. wandering set for `a_t` is null. -/

namespace Monod.Dev.CG.A4

open MeasureTheory Matrix OnePoint Set Filter

variable {A : Subring ℝ}

/-! ### The Möbius action of `ell t` -/

/-! ### The invariant weight `w(x) = 1 / (x² - τ x + 1)` -/

/-! ### Change of variables for `x ↦ τ - 1/x` -/

/-! ### Transport to `P¹` -/

end Monod.Dev.CG.A4

namespace Monod.Dev.CG

open MeasureTheory Matrix

end Monod.Dev.CG
end

section
namespace Monod.Dev.CG.A6

open Polynomial

end Monod.Dev.CG.A6

namespace Monod.Dev.CG

open Polynomial

end Monod.Dev.CG
end

section
/-! A5 + A7 of the Carrière–Ghys argument: the ping-pong partition of `SL(2, A)`. -/

namespace Monod.Dev.CG.A57

open Matrix

section PingPong

variable {K : Type} [NormedField K]

variable {E G : SpecialLinearGroup (Fin 2) K}

end PingPong

section Retraction

variable {A : Subring ℝ} (t : A)

end Retraction

end Monod.Dev.CG.A57

namespace Monod.Dev.CG

open Matrix

end Monod.Dev.CG
end

section
/-! # A8: the core of the Carrière–Ghys argument

A left invariant mean `P` on the orbit relation of `SL(2, A)` gives `u = P f_S`, where `f_S` is
the indicator of the pairs `(x, s x)` with `s ∈ S`.  Freeness off a countable set and the
ping-pong properties of `S` give `u + u ∘ b + u ∘ b² ≤ 1` and `1 ≤ u + u ∘ a^m` a.e.; the second
makes `{u < 1/2}` wandering for `a`, hence null, and the first is then contradictory. -/

namespace Monod.Dev.CG.A8

open Monod OnePoint Filter Topology Set MeasureTheory

variable {A : Subring ℝ}

/-! ### Möbius maps (copied from `DynBasic`) -/

/-! ### Measurability on `P¹ × P¹` -/

theorem secondCountable_P1 : SecondCountableTopology (OnePoint ℝ) :=
  (onePointEquivSphereOfFinrankEq (ι := Fin 2) (V := ℝ) (by simp)).isEmbedding.secondCountableTopology

attribute [local instance] secondCountable_P1

theorem countable_SL (A : Subring ℝ) [Countable A] :
    Countable (Matrix.SpecialLinearGroup (Fin 2) A) :=
  inferInstanceAs (Countable {M : Fin 2 → Fin 2 → A // Matrix.det M = 1})

attribute [local instance] countable_SL

section Bdd

variable {X : Type*} [MeasurableSpace X]

end Bdd

/-! ### The global partial transformations `φ_g` -/

/-! ### Null sets of `volP1` -/

/-! ### Freeness off a countable set -/

/-! ### The two pointwise inequalities -/

end Monod.Dev.CG.A8

namespace Monod.Dev.CG

open MeasureTheory Matrix

end Monod.Dev.CG
end

section
/-! # Group S2: statements 1, 3, 6, 7, 8, 10 of the Lodha–Moore development -/

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod OnePoint Filter Topology Set

/-! ### Möbius maps over `⊤ : Subring ℝ` -/

/-- The real entries of a matrix of `SL(2, A)`. -/
noncomputable abbrev ent {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) (i j : Fin 2) :
    ℝ := ((g i j : A) : ℝ)

/-- A matrix of `SL(2, ℝ)` (over `⊤ : Subring ℝ`) from its real entries. -/
noncomputable def mk2 (p q r s : ℝ) (h : p * s - q * r = 1) :
    Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ) :=
  ⟨!![⟨p, trivial⟩, ⟨q, trivial⟩; ⟨r, trivial⟩, ⟨s, trivial⟩], by
    rw [Matrix.det_fin_two_of]
    ext
    simpa using h⟩

@[simp] lemma ent_mk2_00 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 0 0 = p := rfl
@[simp] lemma ent_mk2_01 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 0 1 = q := rfl
@[simp] lemma ent_mk2_10 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 1 0 = r := rfl
@[simp] lemma ent_mk2_11 (p q r s : ℝ) (h) : ent (mk2 p q r s h) 1 1 = s := rfl

/-! ### Statement 1: `G₀ ≤ H` -/

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Filter Topology Set
open scoped ENNReal

/-! ### Statement 3: `φ` and `Φ` -/

/-- The composite `cfStep ξ(0) ∘ ⋯ ∘ cfStep ξ(n-1)`, evaluated at `x`. -/
noncomputable def Mn (ξ : Stream' Bool) (n : ℕ) (x : ℝ≥0∞) : ℝ≥0∞ :=
  ((List.range n).map ξ).foldr cfStep x

lemma foldr_range_succ {β : Type*} (f : Bool → β → β) (ξ : ℕ → Bool) (n : ℕ) (x : β) :
    ((List.range (n + 1)).map ξ).foldr f x = ((List.range n).map ξ).foldr f (f (ξ n) x) := by
  rw [List.range_succ, List.map_append, List.foldr_append]
  rfl

lemma foldr_range_cons' {β : Type*} (f : Bool → β → β) (g h : ℕ → Bool) (n : ℕ)
    (x : β) (hg : ∀ i, g (i + 1) = h i) :
    ((List.range (n + 1)).map g).foldr f x = f (g 0) (((List.range n).map h).foldr f x) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  have : g ∘ Nat.succ = h := funext hg
  rw [this]
  rfl

lemma foldr_range_cons {β : Type*} (f : Bool → β → β) (d : Bool) (ξ : Stream' Bool) (n : ℕ)
    (x : β) :
    ((List.range (n + 1)).map (Stream'.cons d ξ)).foldr f x =
      f d (((List.range n).map ξ).foldr f x) :=
  foldr_range_cons' f (Stream'.cons d ξ) ξ n x (fun _ => rfl)

lemma Mn_succ (ξ : Stream' Bool) (n : ℕ) (x : ℝ≥0∞) : Mn ξ (n + 1) x = Mn ξ n (cfStep (ξ n) x) :=
  foldr_range_succ _ _ _ _

lemma Mn_cons (d : Bool) (ξ : Stream' Bool) (n : ℕ) (x : ℝ≥0∞) :
    Mn (Stream'.cons d ξ) (n + 1) x = cfStep d (Mn ξ n x) :=
  foldr_range_cons _ _ _ _ _

lemma cfStep_mono (d : Bool) : Monotone (cfStep d) := by
  intro x y h
  cases d
  · simp only [cfStep, Bool.false_eq_true, if_false]
    have := ENNReal.inv_le_inv.2 h
    exact ENNReal.inv_le_inv.2 (by gcongr)
  · simp only [cfStep, if_true]
    gcongr

lemma foldr_mono (l : List Bool) : Monotone (fun x => l.foldr cfStep x) := by
  induction l with
  | nil => exact monotone_id
  | cons a l ih => exact (cfStep_mono a).comp ih

lemma Mn_mono (ξ : Stream' Bool) (n : ℕ) : Monotone (Mn ξ n) := foldr_mono _

/-- The coordinate `t ↦ t / (1 + t)` of `[0, ∞]`, onto `[0, 1]`. -/
noncomputable def U (t : ℝ≥0∞) : ℝ := ((1 + t⁻¹)⁻¹).toReal

lemma U_top : U ⊤ = 1 := by simp [U]

lemma U_of_ne_top {t : ℝ≥0∞} (h : t ≠ ⊤) : U t = t.toReal / (1 + t.toReal) := by
  unfold U
  by_cases h0 : t = 0
  · subst h0; simp
  · have hpos : 0 < t.toReal := ENNReal.toReal_pos h0 h
    rw [ENNReal.toReal_inv, ENNReal.toReal_add (by simp) (by simpa using h0), ENNReal.toReal_inv]
    simp only [ENNReal.toReal_one]
    field_simp
    ring

lemma U_zero : U 0 = 0 := by rw [U_of_ne_top (by simp)]; simp

lemma U_strictMono : StrictMono U := by
  intro x y hxy
  unfold U
  have h1 : (1 + x⁻¹)⁻¹ < (1 + y⁻¹)⁻¹ := by
    apply ENNReal.inv_lt_inv.2
    exact ENNReal.add_lt_add_left ENNReal.one_ne_top (ENNReal.inv_lt_inv.2 hxy)
  have h2 : (1 + y⁻¹)⁻¹ ≠ ⊤ := by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (ENNReal.inv_le_one.2 le_self_add)
  exact (ENNReal.toReal_lt_toReal (ne_top_of_lt h1) h2).2 h1

/-- The digit maps in the coordinate `U`. -/
noncomputable def v : Bool → ℝ → ℝ
  | true, u => 1 / (2 - u)
  | false, u => u / (1 + u)

lemma U_cfStep (d : Bool) (t : ℝ≥0∞) : U (cfStep d t) = v d (U t) := by
  cases d
  · simp only [cfStep, Bool.false_eq_true, if_false, v]
    have hne : (1 + t⁻¹)⁻¹ ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (ENNReal.inv_le_one.2 le_self_add)
    rw [U_of_ne_top hne]
    rfl
  · simp only [cfStep, if_true, v]
    by_cases ht : t = ⊤
    · subst ht; simp [U_top]; norm_num
    · rw [U_of_ne_top ht, U_of_ne_top (by simpa using ht),
        ENNReal.toReal_add ENNReal.one_ne_top ht]
      have hr := ENNReal.toReal_nonneg (a := t)
      simp only [ENNReal.toReal_one]
      have e : 2 - t.toReal / (1 + t.toReal) = (2 + t.toReal) / (1 + t.toReal) := by
        field_simp; ring
      rw [e, one_div_div]
      congr 1
      ring

/-- The composite of the digit maps in the coordinate `U`. -/
noncomputable def Vn (ξ : Stream' Bool) (n : ℕ) (u : ℝ) : ℝ := ((List.range n).map ξ).foldr v u

lemma U_foldr (l : List Bool) (x : ℝ≥0∞) : U (l.foldr cfStep x) = l.foldr v (U x) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, U_cfStep, ih]

lemma U_Mn (ξ : Stream' Bool) (n : ℕ) (x : ℝ≥0∞) : U (Mn ξ n x) = Vn ξ n (U x) := U_foldr _ _

/-- The Farey interval `[q/B, p/A]` after `n` digits. -/
structure FS where
  p : ℕ
  A : ℕ
  q : ℕ
  B : ℕ

/-- One digit: the left (`0`) or right (`1`) half at the mediant. -/
def FS.step : Bool → FS → FS
  | true, ⟨p, A, q, B⟩ => ⟨p, A, p + q, A + B⟩
  | false, ⟨p, A, q, B⟩ => ⟨p + q, A + B, q, B⟩

/-- The Farey interval of the first `n` digits of `ξ`. -/
def fs (ξ : Stream' Bool) : ℕ → FS
  | 0 => ⟨1, 1, 0, 1⟩
  | n + 1 => (fs ξ n).step (ξ n)

lemma fs_spec (ξ : Stream' Bool) (n : ℕ) :
    (fs ξ n).p * (fs ξ n).B = (fs ξ n).q * (fs ξ n).A + 1 ∧ 1 ≤ (fs ξ n).A ∧ 1 ≤ (fs ξ n).B ∧
      n + 2 ≤ (fs ξ n).A + (fs ξ n).B ∧
      ∀ u ∈ Icc (0 : ℝ) 1, Vn ξ n u = (((fs ξ n).p - (fs ξ n).q : ℝ) * u + (fs ξ n).q) /
        (((fs ξ n).A - (fs ξ n).B : ℝ) * u + (fs ξ n).B) := by
  induction n with
  | zero =>
    refine ⟨by simp [fs], by simp [fs], by simp [fs], by simp [fs], fun u _ => ?_⟩
    simp only [fs, Nat.cast_one, Nat.cast_zero]
    show u = _
    ring
  | succ n ih =>
    obtain ⟨hdet, hA, hB, hAB, hV⟩ := ih
    have hV' : ∀ u, Vn ξ (n + 1) u = Vn ξ n (v (ξ n) u) := fun u => foldr_range_succ _ _ _ _
    rcases h : fs ξ n with ⟨p, A, q, B⟩
    rw [h] at hdet hA hB hAB hV
    simp only at hdet hA hB hAB hV
    cases hd : ξ n
    · have hs : fs ξ (n + 1) = ⟨p + q, A + B, q, B⟩ := by simp [fs, h, hd, FS.step]
      rw [hs]
      refine ⟨by simp only; nlinarith, by simp only; omega, by simp only; omega,
        by simp only; omega, fun u hu => ?_⟩
      obtain ⟨hu0, hu1⟩ := hu
      have hmem : u / (1 + u) ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hu0 (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩
      rw [hV', hd, v, hV _ hmem]
      have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
      have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
      have h1 : (0 : ℝ) < 1 + u := by linarith
      have h2 : (0 : ℝ) < A * u + B := by nlinarith
      have h3 : ((A : ℝ) - B) * (u / (1 + u)) + B = (A * u + B) / (1 + u) := by
        field_simp; ring
      have h4 : ((p : ℝ) - q) * (u / (1 + u)) + q = (p * u + q) / (1 + u) := by
        field_simp; ring
      rw [h3, h4, div_div_div_cancel_right₀ h1.ne']
      congr 1 <;> push_cast <;> ring
    · have hs : fs ξ (n + 1) = ⟨p, A, p + q, A + B⟩ := by simp [fs, h, hd, FS.step]
      rw [hs]
      refine ⟨by simp only; nlinarith, by simp only; omega, by simp only; omega,
        by simp only; omega, fun u hu => ?_⟩
      obtain ⟨hu0, hu1⟩ := hu
      have h2u : (0 : ℝ) < 2 - u := by linarith
      have hmem : 1 / (2 - u) ∈ Icc (0 : ℝ) 1 :=
        ⟨by positivity, (div_le_one h2u).2 (by linarith)⟩
      rw [hV', hd, v, hV _ hmem]
      have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
      have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
      have h2 : (0 : ℝ) < A + B - B * u := by nlinarith
      have h3 : ((A : ℝ) - B) * (1 / (2 - u)) + B = (A + B - B * u) / (2 - u) := by
        field_simp; ring
      have h4 : ((p : ℝ) - q) * (1 / (2 - u)) + q = (p + q - q * u) / (2 - u) := by
        field_simp; ring
      rw [h3, h4, div_div_div_cancel_right₀ h2u.ne']
      congr 1 <;> push_cast <;> ring

/-- The width of the `n`-th interval in the coordinate `U`. -/
lemma Vn_one_sub_zero_le (ξ : Stream' Bool) (n : ℕ) :
    Vn ξ n 1 - Vn ξ n 0 ≤ 1 / (n + 1) := by
  obtain ⟨hdet, hA, hB, hAB, hV⟩ := fs_spec ξ n
  rw [hV 1 ⟨zero_le_one, le_rfl⟩, hV 0 ⟨le_rfl, zero_le_one⟩]
  set p := (fs ξ n).p
  set A := (fs ξ n).A
  set q := (fs ξ n).q
  set B := (fs ξ n).B
  have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hdet' : (p : ℝ) * B = q * A + 1 := by exact_mod_cast hdet
  have hAB' : (n : ℝ) + 2 ≤ A + B := by exact_mod_cast hAB
  simp only [mul_one, mul_zero, zero_add, sub_add_cancel]
  have hA0 : (A : ℝ) ≠ 0 := by positivity
  have hB0 : (B : ℝ) ≠ 0 := by positivity
  rw [div_sub_div _ _ hA0 hB0, show (p : ℝ) * B - A * q = 1 by linarith]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

lemma lo_mono (ξ : Stream' Bool) : Monotone (fun n => Mn ξ n 0) :=
  monotone_nat_of_le_succ fun n => by
    simp only [Mn_succ]
    exact Mn_mono ξ n zero_le

lemma hi_anti (ξ : Stream' Bool) : Antitone (fun n => Mn ξ n ⊤) :=
  antitone_nat_of_succ_le fun n => by
    simp only [Mn_succ]
    exact Mn_mono ξ n le_top

lemma lo_le_hi (ξ : Stream' Bool) (m n : ℕ) : Mn ξ m 0 ≤ Mn ξ n ⊤ :=
  (lo_mono ξ (le_max_left m n)).trans
    ((Mn_mono ξ _ zero_le).trans (hi_anti ξ (le_max_right m n)))

/-- Two points in all the intervals `[Mn ξ n 0, Mn ξ n ⊤]` are equal. -/
lemma eq_of_mem_all {ξ : Stream' Bool} {x y : ℝ≥0∞}
    (hx : ∀ n, Mn ξ n 0 ≤ x ∧ x ≤ Mn ξ n ⊤) (hy : ∀ n, Mn ξ n 0 ≤ y ∧ y ≤ Mn ξ n ⊤) :
    x = y := by
  have key : ∀ n : ℕ, |U x - U y| ≤ 1 / (n + 1) := by
    intro n
    have e0 : U (Mn ξ n 0) = Vn ξ n 0 := by rw [U_Mn, U_zero]
    have e1 : U (Mn ξ n ⊤) = Vn ξ n 1 := by rw [U_Mn, U_top]
    have hx0 := U_strictMono.monotone (hx n).1
    have hx1 := U_strictMono.monotone (hx n).2
    have hy0 := U_strictMono.monotone (hy n).1
    have hy1 := U_strictMono.monotone (hy n).2
    rw [e0] at hx0 hy0
    rw [e1] at hx1 hy1
    have hw := Vn_one_sub_zero_le ξ n
    rw [abs_le]
    constructor <;> linarith
  have hU : U x = U y := by
    by_contra hne
    have hpos : 0 < |U x - U y| := abs_pos.2 (sub_ne_zero.2 hne)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    linarith [key n]
  exact U_strictMono.injective hU

lemma phi_spec (ξ : Stream' Bool) :
    Tendsto (cfApprox ξ) atTop (𝓝 (phi ξ)) ∧ ∀ n, Mn ξ n 0 ≤ phi ξ ∧ phi ξ ≤ Mn ξ n ⊤ := by
  set L := ⨆ n, Mn ξ n 0 with hL_def
  set H := ⨅ n, Mn ξ n ⊤ with hH_def
  have hL : ∀ n, Mn ξ n 0 ≤ L ∧ L ≤ Mn ξ n ⊤ := fun n =>
    ⟨le_iSup (fun n => Mn ξ n 0) n, iSup_le fun m => lo_le_hi ξ m n⟩
  have hH : ∀ n, Mn ξ n 0 ≤ H ∧ H ≤ Mn ξ n ⊤ := fun n =>
    ⟨le_iInf fun m => lo_le_hi ξ n m, iInf_le (fun n => Mn ξ n ⊤) n⟩
  have hLH : L = H := eq_of_mem_all hL hH
  have ht : Tendsto (cfApprox ξ) atTop (𝓝 L) := by
    have h1 : Tendsto (fun n => Mn ξ n 0) atTop (𝓝 L) := tendsto_atTop_iSup (lo_mono ξ)
    have h2 : Tendsto (fun n => Mn ξ n ⊤) atTop (𝓝 H) := tendsto_atTop_iInf (hi_anti ξ)
    rw [← hLH] at h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le h1 h2 (fun n => ?_) (fun n => ?_)
    · exact Mn_mono ξ n zero_le
    · exact Mn_mono ξ n le_top
  have hphi : phi ξ = L := ht.limUnder_eq
  rw [hphi]
  exact ⟨ht, hL⟩

lemma eq_phi_of_mem {ξ : Stream' Bool} {x : ℝ≥0∞} (h : ∀ n, Mn ξ n 0 ≤ x ∧ x ≤ Mn ξ n ⊤) :
    x = phi ξ :=
  eq_of_mem_all h (phi_spec ξ).2

lemma phi_cons (d : Bool) (ξ : Stream' Bool) : phi (Stream'.cons d ξ) = cfStep d (phi ξ) := by
  symm
  apply eq_phi_of_mem
  intro n
  cases n with
  | zero => exact ⟨zero_le, le_top⟩
  | succ n =>
    rw [Mn_cons, Mn_cons]
    exact ⟨cfStep_mono d ((phi_spec ξ).2 n).1, cfStep_mono d ((phi_spec ξ).2 n).2⟩

lemma drop_eq_cons (ξ : Stream' Bool) (n : ℕ) :
    ξ.drop n = Stream'.cons (ξ n) (ξ.drop (n + 1)) := by
  funext i
  cases i with
  | zero => simp [Stream'.drop, Stream'.cons, Stream'.get]
  | succ i =>
    simp only [Stream'.drop, Stream'.cons, Stream'.get]
    congr 1
    omega

lemma psi_eq_Mn (ψ : Stream' Bool → ℝ≥0∞)
    (hψ : ∀ d ξ, ψ (Stream'.cons d ξ) = cfStep d (ψ ξ)) (ξ : Stream' Bool) (n : ℕ) :
    ψ ξ = Mn ξ n (ψ (ξ.drop n)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Mn_succ, ← hψ, ← drop_eq_cons]; exact ih

lemma eq_phi_of_eqns (ψ : Stream' Bool → ℝ≥0∞)
    (hψ : ∀ d ξ, ψ (Stream'.cons d ξ) = cfStep d (ψ ξ)) : ψ = phi := by
  funext ξ
  apply eq_phi_of_mem
  intro n
  rw [psi_eq_Mn ψ hψ ξ n]
  exact ⟨Mn_mono ξ n zero_le, Mn_mono ξ n le_top⟩

lemma phi_drop (ξ : Stream' Bool) (n : ℕ) : phi ξ = Mn ξ n (phi (ξ.drop n)) :=
  psi_eq_Mn phi phi_cons ξ n

lemma eq_top_of_eq_one_add {x : ℝ≥0∞} (h : x = 1 + x) : x = ⊤ := by
  by_contra hx
  have h1 : (1 : ℝ≥0∞) + x = 0 + x := by rw [← h, zero_add]
  have := (ENNReal.add_left_inj hx).1 h1
  exact one_ne_zero this

lemma phi_const_true : phi (Stream'.const true) = ⊤ := by
  have h := phi_cons true (Stream'.const true)
  rw [← Stream'.const_eq] at h
  simp only [cfStep, if_true] at h
  exact eq_top_of_eq_one_add h

lemma phi_const_false : phi (Stream'.const false) = 0 := by
  have h := phi_cons false (Stream'.const false)
  rw [← Stream'.const_eq] at h
  simp only [cfStep, Bool.false_eq_true, if_false] at h
  have h2 : (phi (Stream'.const false))⁻¹ = 1 + (phi (Stream'.const false))⁻¹ := by
    conv_lhs => rw [h]
    rw [inv_inv]
  exact ENNReal.inv_eq_top.1 (eq_top_of_eq_one_add h2)

lemma cfStep_lt_top (d : Bool) {x : ℝ≥0∞} (hx : x < ⊤) : cfStep d x < ⊤ := by
  cases d
  · simp only [cfStep, Bool.false_eq_true, if_false]
    exact lt_of_le_of_lt (ENNReal.inv_le_one.2 le_self_add) ENNReal.one_lt_top
  · simp only [cfStep, if_true]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hx⟩

lemma cfStep_pos (d : Bool) {x : ℝ≥0∞} (hx : 0 < x) : 0 < cfStep d x := by
  cases d
  · simp only [cfStep, Bool.false_eq_true, if_false]
    rw [ENNReal.inv_pos]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.inv_ne_top.2 hx.ne'⟩
  · simp only [cfStep, if_true]
    exact lt_of_lt_of_le zero_lt_one le_self_add

lemma foldr_lt_top (l : List Bool) {x : ℝ≥0∞} (hx : x < ⊤) : l.foldr cfStep x < ⊤ := by
  induction l with
  | nil => exact hx
  | cons a l ih => exact cfStep_lt_top a ih

lemma foldr_pos (l : List Bool) {x : ℝ≥0∞} (hx : 0 < x) : 0 < l.foldr cfStep x := by
  induction l with
  | nil => exact hx
  | cons a l ih => exact cfStep_pos a ih

lemma eq_const_true_of_phi_eq_top {ζ : Stream' Bool} (h : phi ζ = ⊤) :
    ζ = Stream'.const true := by
  funext n
  by_contra hn
  have hf : ζ n = false := by
    change ¬ ζ n = true at hn
    simpa using hn
  have h1 := ((phi_spec ζ).2 (n + 1)).2
  rw [Mn_succ, hf, h] at h1
  have h2 : cfStep false ⊤ = 1 := by simp [cfStep]
  rw [h2] at h1
  exact absurd (foldr_lt_top _ ENNReal.one_lt_top) (not_lt.2 h1)

lemma eq_const_false_of_phi_eq_zero {ζ : Stream' Bool} (h : phi ζ = 0) :
    ζ = Stream'.const false := by
  funext n
  by_contra hn
  have hf : ζ n = true := by
    change ¬ ζ n = false at hn
    simpa using hn
  have h1 := ((phi_spec ζ).2 (n + 1)).1
  rw [Mn_succ, hf, h] at h1
  have h2 : cfStep true 0 = 1 := by simp [cfStep]
  rw [h2] at h1
  exact absurd (foldr_pos _ zero_lt_one) (not_lt.2 h1)

lemma cfStep_injective (d : Bool) : Function.Injective (cfStep d) := by
  intro x y h
  cases d
  · simp only [cfStep, Bool.false_eq_true, if_false, inv_inj] at h
    exact inv_inj.1 ((ENNReal.add_right_inj ENNReal.one_ne_top).1 h)
  · simp only [cfStep, if_true] at h
    exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 h

lemma foldr_injective (l : List Bool) : Function.Injective (fun x => l.foldr cfStep x) := by
  induction l with
  | nil => exact Function.injective_id
  | cons a l ih => exact (cfStep_injective a).comp ih

lemma Mn_injective (ξ : Stream' Bool) (n : ℕ) : Function.Injective (Mn ξ n) := foldr_injective _

lemma Mn_congr {ζ η : Stream' Bool} {n : ℕ} (h : ∀ i < n, ζ i = η i) : Mn ζ n = Mn η n := by
  funext x
  unfold Mn
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.1 hi)

lemma cfStep_false_le_one (x : ℝ≥0∞) : cfStep false x ≤ 1 := by
  simp only [cfStep, Bool.false_eq_true, if_false]
  exact ENNReal.inv_le_one.2 le_self_add

lemma one_le_cfStep_true (x : ℝ≥0∞) : 1 ≤ cfStep true x := by
  simp only [cfStep, if_true]
  exact le_self_add

lemma eq_top_of_cfStep_false_eq_one {x : ℝ≥0∞} (h : cfStep false x = 1) : x = ⊤ := by
  simp only [cfStep, Bool.false_eq_true, if_false] at h
  have h3 : 1 + x⁻¹ = 1 := by
    rw [← inv_inv (1 + x⁻¹), h]; simp
  have h2 : 1 + x⁻¹ = 1 + 0 := by rw [h3, add_zero]
  have := (ENNReal.add_right_inj ENNReal.one_ne_top).1 h2
  exact ENNReal.inv_eq_zero.1 this

lemma eq_zero_of_cfStep_true_eq_one {x : ℝ≥0∞} (h : cfStep true x = 1) : x = 0 := by
  simp only [cfStep, if_true] at h
  have h2 : 1 + x = 1 + 0 := by rw [h, add_zero]
  exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 h2

/-- `ζ = t⌢01̄` and `η = t⌢10̄`. -/
def Pair (ζ η : Stream' Bool) : Prop :=
  ∃ t : Seq, ζ = t ++ₛ Stream'.cons false (Stream'.const true) ∧
    η = t ++ₛ Stream'.cons true (Stream'.const false)

lemma take_eq_take {ζ η : Stream' Bool} {n : ℕ} (h : ∀ i < n, ζ i = η i) :
    ζ.take n = η.take n := by
  apply List.ext_getElem (by simp [Stream'.length_take])
  intro i h1 h2
  rw [Stream'.take_get, Stream'.take_get]
  exact h i (by simpa [Stream'.length_take] using h1)

lemma eq_take_append (ζ : Stream' Bool) (n : ℕ) :
    ζ = ζ.take n ++ₛ Stream'.cons (ζ n) (ζ.drop (n + 1)) := by
  rw [← drop_eq_cons, Stream'.append_take_drop]

lemma phi_fiber {ζ η : Stream' Bool} (h : phi ζ = phi η) : ζ = η ∨ Pair ζ η ∨ Pair η ζ := by
  by_cases heq : ζ = η
  · exact Or.inl heq
  right
  have hex : ∃ n, ζ n ≠ η n := by
    by_contra hc
    push Not at hc
    exact heq (funext hc)
  classical
  set n := Nat.find hex with hn_def
  have hn : ζ n ≠ η n := Nat.find_spec hex
  have hlt : ∀ i < n, ζ i = η i := fun i hi => by
    by_contra hc
    exact Nat.find_min hex hi hc
  have h1 : phi (ζ.drop n) = phi (η.drop n) := by
    rw [phi_drop ζ n, phi_drop η n, Mn_congr hlt] at h
    exact Mn_injective η n h
  rw [drop_eq_cons ζ n, drop_eq_cons η n, phi_cons, phi_cons] at h1
  have ht := take_eq_take hlt
  have hζ := eq_take_append ζ n
  have hη := eq_take_append η n
  rw [← ht] at hη
  cases hζn : ζ n <;> cases hηn : η n
  · exact absurd (hζn.trans hηn.symm) hn
  · rw [hζn, hηn] at h1
    have e1 : cfStep false (phi (ζ.drop (n + 1))) = 1 :=
      le_antisymm (cfStep_false_le_one _) (h1 ▸ one_le_cfStep_true _)
    have e2 : cfStep true (phi (η.drop (n + 1))) = 1 := h1 ▸ e1
    have z1 := eq_const_true_of_phi_eq_top (eq_top_of_cfStep_false_eq_one e1)
    have z2 := eq_const_false_of_phi_eq_zero (eq_zero_of_cfStep_true_eq_one e2)
    left
    refine ⟨ζ.take n, hζ.trans ?_, hη.trans ?_⟩
    · rw [hζn, z1]
    · rw [hηn, z2]
  · rw [hζn, hηn] at h1
    have e2 : cfStep false (phi (η.drop (n + 1))) = 1 :=
      le_antisymm (cfStep_false_le_one _) (h1 ▸ one_le_cfStep_true _)
    have e1 : cfStep true (phi (ζ.drop (n + 1))) = 1 := h1 ▸ e2
    have z1 := eq_const_false_of_phi_eq_zero (eq_zero_of_cfStep_true_eq_one e1)
    have z2 := eq_const_true_of_phi_eq_top (eq_top_of_cfStep_false_eq_one e2)
    right
    refine ⟨ζ.take n, hη.trans ?_, hζ.trans ?_⟩
    · rw [hηn, z2]
    · rw [hζn, z1]
  · exact absurd (hζn.trans hηn.symm) hn

/-- `-x` on the projective line for `x ∈ [0, ∞]`, `∞ ↦ ∞`. -/
noncomputable def negP1 (x : ℝ≥0∞) : OnePoint ℝ :=
  if x = ⊤ then OnePoint.infty else ((-x.toReal : ℝ) : OnePoint ℝ)

/-- The complement `ξ̃` of an infinite sequence. -/
def compl (ζ : Stream' Bool) : Stream' Bool := fun n => !ζ n

lemma Phi_cons_true (ζ : Stream' Bool) : Phi (Stream'.cons true ζ) = toP1 (phi ζ) := rfl

lemma Phi_cons_false (ζ : Stream' Bool) : Phi (Stream'.cons false ζ) = negP1 (phi (compl ζ)) :=
  rfl

lemma toP1_injective : Function.Injective toP1 := by
  intro x y h
  unfold toP1 at h
  by_cases hx : x = ⊤ <;> by_cases hy : y = ⊤
  · rw [hx, hy]
  · rw [if_pos hx, if_neg hy] at h; exact absurd h.symm (OnePoint.coe_ne_infty _)
  · rw [if_neg hx, if_pos hy] at h; exact absurd h (OnePoint.coe_ne_infty _)
  · rw [if_neg hx, if_neg hy] at h
    exact (ENNReal.toReal_eq_toReal_iff' hx hy).1 (OnePoint.coe_injective h)

lemma negP1_injective : Function.Injective negP1 := by
  intro x y h
  unfold negP1 at h
  by_cases hx : x = ⊤ <;> by_cases hy : y = ⊤
  · rw [hx, hy]
  · rw [if_pos hx, if_neg hy] at h; exact absurd h.symm (OnePoint.coe_ne_infty _)
  · rw [if_neg hx, if_pos hy] at h; exact absurd h (OnePoint.coe_ne_infty _)
  · rw [if_neg hx, if_neg hy] at h
    exact (ENNReal.toReal_eq_toReal_iff' hx hy).1 (neg_inj.1 (OnePoint.coe_injective h))

lemma toP1_eq_negP1 {x y : ℝ≥0∞} (h : toP1 x = negP1 y) :
    (x = ⊤ ∧ y = ⊤) ∨ (x = 0 ∧ y = 0) := by
  unfold toP1 negP1 at h
  by_cases hx : x = ⊤ <;> by_cases hy : y = ⊤
  · exact Or.inl ⟨hx, hy⟩
  · rw [if_pos hx, if_neg hy] at h; exact absurd h.symm (OnePoint.coe_ne_infty _)
  · rw [if_neg hx, if_pos hy] at h; exact absurd h (OnePoint.coe_ne_infty _)
  · rw [if_neg hx, if_neg hy] at h
    have e := OnePoint.coe_injective h
    have h1 := ENNReal.toReal_nonneg (a := x)
    have h2 := ENNReal.toReal_nonneg (a := y)
    have hx0 : x.toReal = 0 := by linarith
    have hy0 : y.toReal = 0 := by linarith
    right
    exact ⟨(ENNReal.toReal_eq_zero_iff x).1 hx0 |>.resolve_right hx,
      (ENNReal.toReal_eq_zero_iff y).1 hy0 |>.resolve_right hy⟩

lemma compl_compl (ζ : Stream' Bool) : compl (compl ζ) = ζ := by
  funext n; simp [compl]

lemma compl_injective : Function.Injective compl := fun ζ η h => by
  rw [← compl_compl ζ, h, compl_compl]

lemma compl_cons (d : Bool) (ζ : Stream' Bool) :
    compl (Stream'.cons d ζ) = Stream'.cons (!d) (compl ζ) := by
  funext i
  cases i <;> rfl

lemma compl_const (b : Bool) : compl (Stream'.const b) = Stream'.const (!b) := rfl

lemma compl_append (t : Seq) (ζ : Stream' Bool) : compl (t ++ₛ ζ) = t.map not ++ₛ compl ζ := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    show compl (Stream'.cons a (t ++ₛ ζ)) = Stream'.cons (!a) (t.map not ++ₛ compl ζ)
    rw [compl_cons, ih]

lemma phi_pair (t : Seq) :
    phi (t ++ₛ Stream'.cons false (Stream'.const true)) =
      phi (t ++ₛ Stream'.cons true (Stream'.const false)) := by
  induction t with
  | nil =>
    show phi (Stream'.cons false (Stream'.const true)) = phi (Stream'.cons true (Stream'.const false))
    rw [phi_cons, phi_cons, phi_const_true, phi_const_false]
    simp [cfStep]
  | cons a t ih =>
    show phi (Stream'.cons a _) = phi (Stream'.cons a _)
    rw [phi_cons, phi_cons, ih]

lemma Phi_pair_eq (s : Seq) :
    Phi (s ++ₛ Stream'.cons false (Stream'.const true)) =
      Phi (s ++ₛ Stream'.cons true (Stream'.const false)) := by
  cases s with
  | nil =>
    show Phi (Stream'.cons false (Stream'.const true)) =
      Phi (Stream'.cons true (Stream'.const false))
    rw [Phi_cons_false, Phi_cons_true, compl_const]
    simp only [Bool.not_true, phi_const_false]
    simp [negP1, toP1]
  | cons a s =>
    cases a
    · show Phi (Stream'.cons false _) = Phi (Stream'.cons false _)
      rw [Phi_cons_false, Phi_cons_false, compl_append, compl_append, compl_cons, compl_cons,
        compl_const, compl_const]
      simp only [Bool.not_false, Bool.not_true]
      rw [phi_pair]
    · show Phi (Stream'.cons true _) = Phi (Stream'.cons true _)
      rw [Phi_cons_true, Phi_cons_true, phi_pair]

lemma Phi_const_false : Phi (Stream'.const false) = OnePoint.infty := by
  rw [Stream'.const_eq, Phi_cons_false, compl_const]
  simp [phi_const_true, negP1]

lemma Phi_const_true : Phi (Stream'.const true) = OnePoint.infty := by
  rw [Stream'.const_eq, Phi_cons_true, phi_const_true]
  simp [toP1]

lemma Pair_cons (d : Bool) {ζ η : Stream' Bool} (h : Pair ζ η) :
    Pair (Stream'.cons d ζ) (Stream'.cons d η) := by
  obtain ⟨t, h1, h2⟩ := h
  exact ⟨d :: t, by rw [h1]; rfl, by rw [h2]; rfl⟩

lemma Pair_compl {ζ η : Stream' Bool} (h : Pair ζ η) : Pair (compl η) (compl ζ) := by
  obtain ⟨t, h1, h2⟩ := h
  refine ⟨t.map not, ?_, ?_⟩
  · rw [h2, compl_append, compl_cons, compl_const]; rfl
  · rw [h1, compl_append, compl_cons, compl_const]; rfl

lemma Phi_fiber {η ξ : Stream' Bool} (h : Phi η = Phi ξ) :
    η = ξ ∨ Pair η ξ ∨ Pair ξ η ∨
      (η = Stream'.const false ∧ ξ = Stream'.const true) ∨
      (η = Stream'.const true ∧ ξ = Stream'.const false) := by
  obtain ⟨a, η', rfl⟩ : ∃ a η', η = Stream'.cons a η' := ⟨η.head, η.tail, (Stream'.eta η).symm⟩
  obtain ⟨b, ξ', rfl⟩ : ∃ b ξ', ξ = Stream'.cons b ξ' := ⟨ξ.head, ξ.tail, (Stream'.eta ξ).symm⟩
  cases a <;> cases b
  · rw [Phi_cons_false, Phi_cons_false] at h
    rcases phi_fiber (negP1_injective h) with e | p | p
    · left; rw [compl_injective e]
    · have := Pair_compl p
      rw [compl_compl, compl_compl] at this
      exact Or.inr (Or.inr (Or.inl (Pair_cons false this)))
    · have := Pair_compl p
      rw [compl_compl, compl_compl] at this
      exact Or.inr (Or.inl (Pair_cons false this))
  · rw [Phi_cons_false, Phi_cons_true] at h
    rcases toP1_eq_negP1 h.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := eq_const_true_of_phi_eq_top h1
      have e2 := eq_const_true_of_phi_eq_top h2
      have e3 : η' = Stream'.const false := by rw [← compl_compl η', e2]; rfl
      right; right; right; left
      rw [e1, e3]
      exact ⟨(Stream'.const_eq false).symm, (Stream'.const_eq true).symm⟩
    · have e1 := eq_const_false_of_phi_eq_zero h1
      have e2 := eq_const_false_of_phi_eq_zero h2
      have e3 : η' = Stream'.const true := by rw [← compl_compl η', e2]; rfl
      right; left
      rw [e1, e3]
      exact ⟨[], rfl, rfl⟩
  · rw [Phi_cons_true, Phi_cons_false] at h
    rcases toP1_eq_negP1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := eq_const_true_of_phi_eq_top h1
      have e2 := eq_const_true_of_phi_eq_top h2
      have e3 : ξ' = Stream'.const false := by rw [← compl_compl ξ', e2]; rfl
      right; right; right; right
      rw [e1, e3]
      exact ⟨(Stream'.const_eq true).symm, (Stream'.const_eq false).symm⟩
    · have e1 := eq_const_false_of_phi_eq_zero h1
      have e2 := eq_const_false_of_phi_eq_zero h2
      have e3 : ξ' = Stream'.const true := by rw [← compl_compl ξ', e2]; rfl
      right; right; left
      rw [e1, e3]
      exact ⟨[], rfl, rfl⟩
  · rw [Phi_cons_true, Phi_cons_true] at h
    rcases phi_fiber (toP1_injective h) with e | p | p
    · left; rw [e]
    · exact Or.inr (Or.inl (Pair_cons true p))
    · exact Or.inr (Or.inr (Or.inl (Pair_cons true p)))

lemma app_get (t : Seq) (ζ : Stream' Bool) (k : ℕ) : (t ++ₛ ζ) (t.length + k) = ζ k :=
  Stream'.get_append_right k t ζ

lemma tail_at (t : Seq) (d b : Bool) : (t ++ₛ Stream'.cons d (Stream'.const b)) t.length = d := by
  have := app_get t (Stream'.cons d (Stream'.const b)) 0
  rw [Nat.add_zero] at this
  exact this

lemma tail_ge (t : Seq) (d b : Bool) {p : ℕ} (hp : t.length + 1 ≤ p) :
    (t ++ₛ Stream'.cons d (Stream'.const b)) p = b := by
  obtain ⟨k, rfl⟩ : ∃ k, p = t.length + (k + 1) := ⟨p - t.length - 1, by omega⟩
  rw [app_get]
  rfl

lemma ec_tail (t : Seq) (d b : Bool) : EventuallyConst (t ++ₛ Stream'.cons d (Stream'.const b)) :=
  ⟨t.length + 1, b, fun _ hn => tail_ge t d b hn⟩

lemma pair_ne (t t' : Seq) :
    t ++ₛ Stream'.cons false (Stream'.const true) ≠ t' ++ₛ Stream'.cons true (Stream'.const false) := by
  intro h
  have := congrFun h (t.length + t'.length + 1)
  rw [tail_ge t false true (by omega), tail_ge t' true false (by omega)] at this
  exact Bool.noConfusion this

lemma tail_ne_const (t : Seq) (d b c : Bool) (h : d ≠ c) :
    t ++ₛ Stream'.cons d (Stream'.const b) ≠ Stream'.const c := by
  intro e
  have := congrFun e t.length
  rw [tail_at] at this
  exact h this

lemma tail_ne_const' (t : Seq) (d b c : Bool) (h : b ≠ c) :
    t ++ₛ Stream'.cons d (Stream'.const b) ≠ Stream'.const c := by
  intro e
  have := congrFun e (t.length + 1)
  rw [tail_ge t d b le_rfl] at this
  exact h this

lemma tail_inj {t t' : Seq} {d b : Bool} (hdb : d ≠ b)
    (h : t ++ₛ Stream'.cons d (Stream'.const b) = t' ++ₛ Stream'.cons d (Stream'.const b)) :
    t = t' := by
  rcases lt_trichotomy t.length t'.length with hl | hl | hl
  · have := congrFun h t'.length
    rw [tail_at, tail_ge t d b hl] at this
    exact absurd this.symm hdb
  · exact Stream'.append_left_injective _ _ _ _ h hl
  · have := congrFun h t.length
    rw [tail_at, tail_ge t' d b hl] at this
    exact absurd this hdb

lemma ec_cases (ξ : Stream' Bool) (h : EventuallyConst ξ) :
    ξ = Stream'.const false ∨ ξ = Stream'.const true ∨
      ∃ t : Seq, ξ = t ++ₛ Stream'.cons false (Stream'.const true) ∨
        ξ = t ++ₛ Stream'.cons true (Stream'.const false) := by
  obtain ⟨N, b, hN⟩ := h
  induction N generalizing ξ with
  | zero =>
    have : ξ = Stream'.const b := funext fun n => hN n (Nat.zero_le n)
    cases b
    · exact Or.inl this
    · exact Or.inr (Or.inl this)
  | succ N ih =>
    have htl : ∀ n ≥ N, ξ.tail n = b := fun n hn => hN (n + 1) (by omega)
    have hξ : ξ = Stream'.cons (ξ 0) ξ.tail := (Stream'.eta ξ).symm
    rcases ih ξ.tail htl with e | e | ⟨t, e | e⟩
    · cases h0 : ξ 0
      · left; rw [hξ, h0, e, ← Stream'.const_eq]
      · right; right; exact ⟨[], Or.inr (by rw [hξ, h0, e]; rfl)⟩
    · cases h0 : ξ 0
      · right; right; exact ⟨[], Or.inl (by rw [hξ, h0, e]; rfl)⟩
      · right; left; rw [hξ, h0, e, ← Stream'.const_eq]
    · right; right; exact ⟨ξ 0 :: t, Or.inl (by rw [hξ, e]; rfl)⟩
    · right; right; exact ⟨ξ 0 :: t, Or.inr (by rw [hξ, e]; rfl)⟩

lemma const_ne : Stream'.const false ≠ Stream'.const true := fun h =>
  Bool.noConfusion (congrFun h 0)

lemma Phi_ncard (ξ : Stream' Bool) (h : EventuallyConst ξ) : {η | Phi η = Phi ξ}.ncard = 2 := by
  rcases ec_cases ξ h with rfl | rfl | ⟨t, rfl | rfl⟩
  · have : {η | Phi η = Phi (Stream'.const false)} =
        {Stream'.const false, Stream'.const true} := by
      ext η
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hη
        rcases Phi_fiber hη with e | ⟨t, _, h2⟩ | ⟨t, h1, _⟩ | ⟨e, _⟩ | ⟨e, _⟩
        · exact Or.inl e
        · exact absurd h2.symm (tail_ne_const t true false false (by decide))
        · exact absurd h1.symm (tail_ne_const' t false true false (by decide))
        · exact Or.inl e
        · exact Or.inr e
      · rintro (rfl | rfl)
        · rfl
        · rw [Phi_const_true, Phi_const_false]
    rw [this, Set.ncard_pair const_ne]
  · have : {η | Phi η = Phi (Stream'.const true)} =
        {Stream'.const false, Stream'.const true} := by
      ext η
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hη
        rcases Phi_fiber hη with e | ⟨t, _, h2⟩ | ⟨t, h1, _⟩ | ⟨e, _⟩ | ⟨e, _⟩
        · exact Or.inr e
        · exact absurd h2.symm (tail_ne_const' t true false true (by decide))
        · exact absurd h1.symm (tail_ne_const t false true true (by decide))
        · exact Or.inl e
        · exact Or.inr e
      · rintro (rfl | rfl)
        · rw [Phi_const_true, Phi_const_false]
        · rfl
    rw [this, Set.ncard_pair const_ne]
  · have : {η | Phi η = Phi (t ++ₛ Stream'.cons false (Stream'.const true))} =
        {t ++ₛ Stream'.cons false (Stream'.const true),
          t ++ₛ Stream'.cons true (Stream'.const false)} := by
      ext η
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hη
        rcases Phi_fiber hη with e | ⟨t', _, h2⟩ | ⟨t', h1, h2⟩ | ⟨_, e⟩ | ⟨_, e⟩
        · exact Or.inl e
        · exact absurd h2 (pair_ne t t')
        · right
          rw [h2, tail_inj (by decide) h1]
        · exact absurd e (tail_ne_const t false true true (by decide))
        · exact absurd e (tail_ne_const' t false true false (by decide))
      · rintro (rfl | rfl)
        · rfl
        · exact (Phi_pair_eq t).symm
    rw [this, Set.ncard_pair (pair_ne t t)]
  · have : {η | Phi η = Phi (t ++ₛ Stream'.cons true (Stream'.const false))} =
        {t ++ₛ Stream'.cons true (Stream'.const false),
          t ++ₛ Stream'.cons false (Stream'.const true)} := by
      ext η
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hη
        rcases Phi_fiber hη with e | ⟨t', h1, h2⟩ | ⟨t', h1, _⟩ | ⟨_, e⟩ | ⟨_, e⟩
        · exact Or.inl e
        · right
          rw [h1, tail_inj (by decide) h2]
        · exact absurd h1.symm (pair_ne t' t)
        · exact absurd e (tail_ne_const' t true false true (by decide))
        · exact absurd e (tail_ne_const t true false false (by decide))
      · rintro (rfl | rfl)
        · rfl
        · exact Phi_pair_eq t
    rw [this, Set.ncard_pair (pair_ne t t).symm]

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore MeasureTheory Set
open scoped ENNReal

section Orbit

variable {X : Type*} [MeasurableSpace X] (Γ : Type) [Group Γ] [MulAction Γ X]

variable {Γ}

end Orbit

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2 MeasureTheory Set

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod OnePoint Filter Topology Set Matrix

@[simp] lemma ent_kTrans_00 : ent kTrans 0 0 = 1 := rfl
@[simp] lemma ent_kTrans_01 : ent kTrans 0 1 = 1 := rfl
@[simp] lemma ent_kTrans_10 : ent kTrans 1 0 = 0 := rfl
@[simp] lemma ent_kTrans_11 : ent kTrans 1 1 = 1 := rfl
@[simp] lemma ent_kInv_00 : ent kInv 0 0 = 0 := rfl
@[simp] lemma ent_kInv_01 : ent kInv 0 1 = 1 := rfl
@[simp] lemma ent_kInv_10 : ent kInv 1 0 = -1 := rfl
@[simp] lemma ent_kInv_11 : ent kInv 1 1 = 0 := rfl
@[simp] lemma ent_kDil_00 : ent kDil 0 0 = Real.sqrt 2 := rfl
@[simp] lemma ent_kDil_01 : ent kDil 0 1 = 0 := rfl
@[simp] lemma ent_kDil_10 : ent kDil 1 0 = 0 := rfl
@[simp] lemma ent_kDil_11 : ent kDil 1 1 = 1 / Real.sqrt 2 := rfl

/-! ### Möbius maps are continuous and preserve null sets (from the Monod development) -/

section Mob

variable {A : Subring ℝ}

theorem secondCountable_P1 : SecondCountableTopology (OnePoint ℝ) :=
  (onePointEquivSphereOfFinrankEq (ι := Fin 2) (V := ℝ) (by simp)).isEmbedding.secondCountableTopology

theorem polishSpace_P1 : PolishSpace (OnePoint ℝ) := by
  have e := onePointEquivSphereOfFinrankEq (ι := Fin 2) (V := ℝ) (by simp)
  have : PolishSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    Metric.isClosed_sphere.polishSpace
  exact e.isClosedEmbedding.polishSpace

theorem sigmaFinite_volP1 : MeasureTheory.SigmaFinite volP1 :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding.sigmaFinite_map

end Mob

attribute [local instance] secondCountable_P1 polishSpace_P1 sigmaFinite_volP1

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

attribute [local instance] secondCountable_P1 polishSpace_P1 sigmaFinite_volP1

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod OnePoint Filter Topology Set Matrix

/-! ### Statement 10: `G₀`- and `K`-orbits of irrational points -/

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod OnePoint Filter Topology Set MeasureTheory

/-! ### The Carrière–Ghys ping-pong argument for a countable subgroup `Λ` of `SL(2, ℝ)`

Monod's development (`Monod.Dev.CG.A8`) runs the argument for the orbit relation of `SL(2, A)`;
here it is run for the orbit relation of any countable subgroup `Λ` containing `a_t`, `b_t` and
a ping-pong set `S ⊆ Λ`. -/

section CGL

attribute [local instance] secondCountable_P1

variable {Λ}

end CGL


/-! ### The Carrière–Ghys argument for `K` -/

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

attribute [local instance] secondCountable_P1 polishSpace_P1 sigmaFinite_volP1

end LodhaMoore

namespace LodhaMoore.Dev.S2

open LodhaMoore Monod MeasureTheory

end LodhaMoore.Dev.S2

namespace LodhaMoore

open LodhaMoore.Dev.S2

attribute [local instance] secondCountable_P1 polishSpace_P1 sigmaFinite_volP1

end LodhaMoore
end

section
open LodhaMoore
open LodhaMoore.Dev.S2
theorem solution :
    (∀ ξ, phi (Stream'.cons false ξ) = (1 + (phi ξ)⁻¹)⁻¹) ∧ (∀ ξ, phi (Stream'.cons true ξ) = 1 + phi ξ) ∧
    (∀ ψ : Stream' Bool → ENNReal, (∀ ξ, ψ (Stream'.cons false ξ) = (1 + (ψ ξ)⁻¹)⁻¹) →
      (∀ ξ, ψ (Stream'.cons true ξ) = 1 + ψ ξ) → ψ = phi) ∧
    (∀ ξ, ¬ EventuallyConst ξ → ∀ η, Phi η = Phi ξ → η = ξ) ∧
    (∀ ξ, EventuallyConst ξ → {η | Phi η = Phi ξ}.ncard = 2) ∧
    (∀ s : Seq, Phi (s ++ₛ Stream'.cons false (Stream'.const true)) =
      Phi (s ++ₛ Stream'.cons true (Stream'.const false))) ∧
    Phi (Stream'.const false) = OnePoint.infty ∧ Phi (Stream'.const true) = OnePoint.infty := by
  refine ⟨fun ξ => phi_cons false ξ, fun ξ => phi_cons true ξ, fun ψ h0 h1 => ?_,
    fun ξ hξ η hη => ?_, Phi_ncard, Phi_pair_eq, Phi_const_false, Phi_const_true⟩
  · exact eq_phi_of_eqns ψ fun d ξ => by cases d; exacts [h0 ξ, h1 ξ]
  · rcases Phi_fiber hη with e | ⟨t, _, h2⟩ | ⟨t, h1, _⟩ | ⟨_, e⟩ | ⟨_, e⟩
    · exact e
    · exact absurd (h2 ▸ ec_tail t true false) hξ
    · exact absurd (h1 ▸ ec_tail t false true) hξ
    · exact absurd (e ▸ ⟨0, true, fun _ _ => rfl⟩) hξ
    · exact absurd (e ▸ ⟨0, false, fun _ _ => rfl⟩) hξ
end
