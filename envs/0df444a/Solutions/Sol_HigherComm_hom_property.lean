-- Prove2me | solution 1 for HigherComm.hom_property
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-07T08:12:04.704999+00:00
-- url     : https://prove2.me/submissions/ae3f8ef2-621e-483f-a04e-73d7eaad37b3

import Definitions.Def_HigherComm_defs
import Mathlib.Tactic.FinCases
import Theorems.Thm_HigherComm_additivity
import Theorems.Thm_HigherComm_higherComm_perm
import Theorems.Thm_HigherComm_centralAt_iff_le

universe u₁ v₁ w₁ x₁

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

namespace HigherComm
namespace HCHom

variable {L : FirstOrder.Language.{u₁, v₁}} {M : Type w₁} [L.Structure M] [L.IsAlgebraic]

/-! ### Lattice helpers -/

theorem cong_ext {φ ψ : Congruence (L := L) M} (h : ∀ x y, φ.r x y ↔ ψ.r x y) : φ = ψ := by
  obtain ⟨⟨r, hr⟩, f1, r1⟩ := φ
  obtain ⟨⟨s, hs⟩, f2, r2⟩ := ψ
  have : r = s := funext fun x => funext fun y => propext (h x y)
  subst this
  rfl

theorem le_refl' (φ : Congruence (L := L) M) : φ ≤ φ := fun _ _ h => h

theorem le_trans' {a b c : Congruence (L := L) M} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  fun x y h => h2 x y (h1 x y h)

theorem iSup_le' {ι : Sort*} (γ : ι → Congruence (L := L) M) (α : Congruence (L := L) M)
    (h : ∀ i, γ i ≤ α) : Congruence.iSup γ ≤ α := fun x y hxy => hxy α h

theorem le_sup_left' (φ ψ : Congruence (L := L) M) : φ ≤ φ.sup ψ :=
  fun x y h χ hχ => hχ true x y h

theorem le_sup_right' (φ ψ : Congruence (L := L) M) : ψ ≤ φ.sup ψ :=
  fun x y h χ hχ => hχ false x y h

theorem realize_rel (δ : Congruence (L := L) M) {α : Type*} (t : L.Term α) {x y : α → M}
    (h : ∀ a, δ.r (x a) (y a)) : δ.r (t.realize x) (t.realize y) := by
  induction t with
  | var a => exact h a
  | func f ts ih => exact δ.fun_compat f _ _ ih

/-! ### Centrality basics -/

/-- `M(T) ⊆ M(T')` when `T ≤ T'` coordinatewise, so centrality passes down. -/
theorem centralAt_mono {K : ℕ} {T T' : Fin K → Congruence (L := L) M}
    (hTT : ∀ j x y, (T' j).r x y → (T j).r x y) {j : Fin K} {δ : Congruence (L := L) M}
    (h : CentralAt T j δ) : CentralAt T' j δ := by
  intro m' hm' hS
  obtain ⟨r, t, a, b, hab, ht⟩ := hm'
  exact h m' ⟨r, t, a, b, fun j p => hTT j _ _ (hab j p), ht⟩ hS

/-- Every `(j)`-line of a `T`-matrix is a `θ_j`-pair; in particular `C(T; j; θ_j)`. -/
theorem centralAt_self {K : ℕ} (T : Fin K → Congruence (L := L) M) (j : Fin K) :
    CentralAt T j (T j) := by
  intro h hh _
  obtain ⟨r, t, a, b, hab, ht⟩ := hh
  unfold PivotRel LineRel
  rw [ht, ht]
  unfold cubeEval
  apply realize_rel
  intro x
  rcases x with ⟨i, p⟩ | c
  · by_cases hi : i = j
    · subst hi
      simpa using hab i p
    · simp only [Sum.elim_inl, Function.update_of_ne hi]
      exact (T j).iseqv.refl _
  · exact (T j).iseqv.refl _

/-- `[T] ≤ θ_last`. -/
theorem le_last {k : ℕ} (T : Fin (k + 2) → Congruence (L := L) M) :
    higherComm T ≤ T (Fin.last (k + 1)) :=
  fun x y hxy => hxy _ (centralAt_self T _)

/-! ### Enlarging the arguments by `π ≤ α` (uses additivity and permutation invariance) -/

theorem enlarge_last {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : IsDayTerms M m)
    (θ : Fin (k + 1) → Congruence (L := L) M) (γ π α : Congruence (L := L) M) (hπα : π ≤ α)
    (h : higherComm (Fin.snoc θ γ : Fin (k + 2) → Congruence (L := L) M) ≤ α) :
    higherComm (Fin.snoc θ (γ.sup π) : Fin (k + 2) → Congruence (L := L) M) ≤ α := by
  show higherComm (Fin.snoc θ (Congruence.iSup (fun b : Bool => cond b γ π)) :
    Fin (k + 2) → Congruence (L := L) M) ≤ α
  rw [HigherComm.additivity m hm θ]
  apply iSup_le'
  intro b
  cases b
  · have e : (Fin.snoc θ (cond false γ π) : Fin (k + 2) → Congruence (L := L) M)
        (Fin.last (k + 1)) = π := by simp [Fin.snoc]
    refine le_trans' (le_last _) ?_
    rw [e]
    exact hπα
  · exact h

theorem enlarge_coord {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : IsDayTerms M m)
    (T : Fin (k + 2) → Congruence (L := L) M) (i : Fin (k + 2)) (π α : Congruence (L := L) M)
    (hπα : π ≤ α) (h : higherComm T ≤ α) :
    higherComm (Function.update T i ((T i).sup π)) ≤ α := by
  let σ : Equiv.Perm (Fin (k + 2)) := Equiv.swap i (Fin.last (k + 1))
  have e : ∀ X : Congruence (L := L) M, Function.update T i X ∘ σ =
      (Fin.snoc (Fin.init (T ∘ σ)) X : Fin (k + 2) → Congruence (L := L) M) := by
    intro X
    funext j
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp [σ, Fin.snoc]
    · have hne : σ j'.castSucc ≠ i := by
        intro heq
        apply Fin.castSucc_ne_last j'
        apply σ.injective
        rw [heq]
        simp [σ]
      rw [Function.comp_apply, Function.update_of_ne hne, Fin.snoc_castSucc]
      rfl
  calc higherComm (Function.update T i ((T i).sup π))
      = higherComm (Function.update T i ((T i).sup π) ∘ σ) :=
        (HigherComm.higherComm_perm m hm _ σ).symm
    _ = higherComm (Fin.snoc (Fin.init (T ∘ σ)) ((T i).sup π) :
        Fin (k + 2) → Congruence (L := L) M) := by rw [e]
    _ ≤ α := enlarge_last m hm _ (T i) π α hπα (by
        rw [← e (T i), Function.update_eq_self, HigherComm.higherComm_perm m hm]
        exact h)

theorem enlarge_all {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : IsDayTerms M m)
    (T : Fin (k + 2) → Congruence (L := L) M) (π α : Congruence (L := L) M)
    (hπα : π ≤ α) (h : higherComm T ≤ α) :
    higherComm (fun i => (T i).sup π) ≤ α := by
  have key : ∀ s, s ≤ k + 2 →
      higherComm (fun i : Fin (k + 2) => if i.val < s then (T i).sup π else T i) ≤ α := by
    intro s
    induction s with
    | zero => intro _; simpa using h
    | succ s ih =>
      intro hs
      have e : (fun i : Fin (k + 2) => if i.val < s + 1 then (T i).sup π else T i) =
          Function.update (fun i : Fin (k + 2) => if i.val < s then (T i).sup π else T i)
            ⟨s, hs⟩ (((fun i : Fin (k + 2) => if i.val < s then (T i).sup π else T i)
              ⟨s, hs⟩).sup π) := by
        funext i
        by_cases hi : i = ⟨s, hs⟩
        · subst hi; simp
        · rw [Function.update_of_ne hi]
          have : i.val ≠ s := fun h' => hi (Fin.ext h')
          by_cases h1 : i.val < s
          · simp [h1, show i.val < s + 1 by omega]
          · simp [h1, show ¬ i.val < s + 1 by omega]
      rw [e]
      exact enlarge_coord m hm _ ⟨s, hs⟩ π α hπα (ih (by omega))
  have e : (fun i : Fin (k + 2) => if i.val < k + 2 then (T i).sup π else T i) =
      fun i => (T i).sup π := funext fun i => if_pos i.isLt
  have := key (k + 2) le_rfl
  rwa [e] at this

/-! ### Surjective homomorphisms -/

section Hom

variable {N : Type x₁} [L.Structure N]

theorem hom_realize (f : M →[L] N) {α : Type*} (t : L.Term α) (v : α → M) :
    f (t.realize v) = t.realize (f ∘ v) := by
  induction t with
  | var a => rfl
  | func g ts ih =>
    show f (funMap g _) = funMap g _
    rw [Hom.map_fun]
    congr 1
    funext i
    exact ih i

/-- Day terms pass to surjective images. -/
theorem isDayTerms_of_surj (f : M →[L] N) (hf : Function.Surjective f) {n : ℕ}
    {m : Fin (n + 1) → L.Term (Fin 4)} (hm : IsDayTerms M m) : IsDayTerms N m := by
  have hR : ∀ (t : L.Term (Fin 4)) (a b c d : M),
      t.realize ![f a, f b, f c, f d] = f (t.realize ![a, b, c, d]) := by
    intro t a b c d
    rw [hom_realize]
    congr 1
    funext q
    fin_cases q <;> rfl
  refine ⟨fun e x y => ?_, fun x y z u => ?_, fun x y z u => ?_, fun e he x u => ?_,
    fun e ho x y u => ?_⟩
  · obtain ⟨x, rfl⟩ := hf x; obtain ⟨y, rfl⟩ := hf y
    rw [hR, hm.1]
  · obtain ⟨x, rfl⟩ := hf x; obtain ⟨y, rfl⟩ := hf y
    obtain ⟨z, rfl⟩ := hf z; obtain ⟨u, rfl⟩ := hf u
    rw [hR, hm.2.1]
  · obtain ⟨x, rfl⟩ := hf x; obtain ⟨y, rfl⟩ := hf y
    obtain ⟨z, rfl⟩ := hf z; obtain ⟨u, rfl⟩ := hf u
    rw [hR, hm.2.2.1]
  · obtain ⟨x, rfl⟩ := hf x; obtain ⟨u, rfl⟩ := hf u
    rw [hR, hR, hm.2.2.2.1 e he]
  · obtain ⟨x, rfl⟩ := hf x; obtain ⟨y, rfl⟩ := hf y; obtain ⟨u, rfl⟩ := hf u
    rw [hR, hR, hm.2.2.2.2 e ho]

/-- The image of a congruence `θ ≥ ker f` under a surjective `f` (already a congruence). -/
def imgCong (f : M →[L] N) (hf : Function.Surjective f) (θ : Congruence (L := L) M)
    (hπ : ∀ x y, f x = f y → θ.r x y) : Congruence (L := L) N where
  r a b := ∃ x y, f x = a ∧ f y = b ∧ θ.r x y
  iseqv :=
    { refl := fun a => by
        obtain ⟨x, rfl⟩ := hf a
        exact ⟨x, x, rfl, rfl, θ.iseqv.refl x⟩
      symm := fun ⟨x, y, hx, hy, h⟩ => ⟨y, x, hy, hx, θ.iseqv.symm h⟩
      trans := fun ⟨x, y, hx, hy, h⟩ ⟨y', z, hy', hz, h'⟩ =>
        ⟨x, z, hx, hz, θ.iseqv.trans h (θ.iseqv.trans (hπ y y' (hy.trans hy'.symm)) h')⟩ }
  fun_compat g a b h := by
    choose x y hx hy hxy using h
    refine ⟨funMap g x, funMap g y, ?_, ?_, θ.fun_compat g x y hxy⟩
    · rw [Hom.map_fun]; congr 1; funext i; exact hx i
    · rw [Hom.map_fun]; congr 1; funext i; exact hy i
  rel_compat R _ _ _ := isEmptyElim R

/-- For `θ ≥ ker f`, `f(θ)` is exactly the image relation. -/
theorem map_iff (f : M →[L] N) (hf : Function.Surjective f) (θ : Congruence (L := L) M)
    (hπ : ∀ x y, f x = f y → θ.r x y) (x y : M) :
    (Congruence.map f θ).r (f x) (f y) ↔ θ.r x y := by
  constructor
  · intro h
    obtain ⟨x', y', hx, hy, h'⟩ := h (imgCong f hf θ hπ) (fun x y hxy => ⟨x, y, rfl, rfl, hxy⟩)
    exact θ.iseqv.trans (hπ x x' hx.symm) (θ.iseqv.trans h' (hπ y' y hy))
  · exact fun h ψ hψ => hψ x y h

/-- `f ∘ M(T) ⊆ M(S)` whenever `f` maps `Tᵢ` into `Sᵢ`. -/
theorem isTMatrix_map (f : M →[L] N) {K : ℕ} (T : Fin K → Congruence (L := L) M)
    (S : Fin K → Congruence (L := L) N) (hTS : ∀ i x y, (T i).r x y → (S i).r (f x) (f y))
    {h : (Fin K → Bool) → M} (hh : IsTMatrix T h) : IsTMatrix S (fun v => f (h v)) := by
  obtain ⟨r, t, a, b, hab, ht⟩ := hh
  refine ⟨r, t.relabel (Sum.map id f), fun i p => f (a i p), fun i p => f (b i p),
    fun i p => hTS i _ _ (hab i p), fun v => ?_⟩
  show f (h v) = _
  rw [ht]
  unfold cubeEval
  rw [hom_realize, Term.realize_relabel]
  congr 1
  funext x
  rcases x with ⟨i, p⟩ | c
  · rcases hv : v i <;> simp [hv]
  · rfl

/-- Every `S`-matrix lifts along a surjective `f` to a `T'`-matrix, when `Sᵢ`-pairs lift to
`T'ᵢ`-pairs. -/
theorem isTMatrix_lift (f : M →[L] N) (hf : Function.Surjective f) {K : ℕ}
    (T' : Fin K → Congruence (L := L) M) (S : Fin K → Congruence (L := L) N)
    (hST : ∀ i a b, (S i).r a b → ∃ x y, f x = a ∧ f y = b ∧ (T' i).r x y)
    {g : (Fin K → Bool) → N} (hg : IsTMatrix S g) :
    ∃ h, IsTMatrix T' h ∧ ∀ v, g v = f (h v) := by
  obtain ⟨r, t, a, b, hab, ht⟩ := hg
  choose x y hx hy hxy using fun i p => hST i _ _ (hab i p)
  refine ⟨fun v => cubeEval (t.relabel (Sum.map id (Function.surjInv hf))) x y v,
    ⟨r, _, x, y, hxy, fun v => rfl⟩, fun v => ?_⟩
  rw [ht]
  unfold cubeEval
  rw [hom_realize, Term.realize_relabel]
  congr 1
  funext z
  rcases z with ⟨i, p⟩ | c
  · rcases hv : v i <;> simp [hv, hx, hy]
  · exact (Function.surjInv_eq hf c).symm

theorem central_comap (f : M →[L] N) {K : ℕ} (T' : Fin K → Congruence (L := L) M)
    (S : Fin K → Congruence (L := L) N) (hTS : ∀ i x y, (T' i).r x y → (S i).r (f x) (f y))
    (j : Fin K) (ε : Congruence (L := L) N) (hC : CentralAt S j ε) :
    CentralAt T' j (Congruence.comap f ε) := by
  intro h hh hS
  exact hC _ (isTMatrix_map f T' S hTS hh) hS

theorem central_map (f : M →[L] N) (hf : Function.Surjective f) {K : ℕ}
    (T' : Fin K → Congruence (L := L) M) (S : Fin K → Congruence (L := L) N)
    (hST : ∀ i a b, (S i).r a b → ∃ x y, f x = a ∧ f y = b ∧ (T' i).r x y)
    (j : Fin K) (α : Congruence (L := L) M) (hπ : ∀ x y, f x = f y → α.r x y)
    (hC : CentralAt T' j α) : CentralAt S j (Congruence.map f α) := by
  intro g hg hS
  obtain ⟨h, hh, hgh⟩ := isTMatrix_lift f hf T' S hST hg
  have hg' : g = fun v => f (h v) := funext hgh
  subst hg'
  have := hC h hh (fun v hv => (map_iff f hf α hπ _ _).mp (hS v hv))
  exact (map_iff f hf α hπ _ _).mpr this

theorem hom_main {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : IsDayTerms M m)
    (f : M →[L] N) (hf : Function.Surjective f) (T : Fin (k + 2) → Congruence (L := L) M) :
    (higherComm T).sup (Congruence.ker f) =
      Congruence.comap f
        (higherComm (fun i => Congruence.map f ((T i).sup (Congruence.ker f)))) := by
  have hmN : IsDayTerms N m := isDayTerms_of_surj f hf hm
  let T' : Fin (k + 2) → Congruence (L := L) M := fun i => (T i).sup (Congruence.ker f)
  let S : Fin (k + 2) → Congruence (L := L) N := fun i => Congruence.map f (T' i)
  have hπT' : ∀ i x y, f x = f y → (T' i).r x y :=
    fun i x y hxy => le_sup_right' (T i) (Congruence.ker f) x y hxy
  have hTS : ∀ i x y, (T' i).r x y → (S i).r (f x) (f y) := fun i x y h ψ hψ => hψ x y h
  have hST : ∀ i a b, (S i).r a b → ∃ x y, f x = a ∧ f y = b ∧ (T' i).r x y := by
    intro i a b hab
    obtain ⟨x, rfl⟩ := hf a
    obtain ⟨y, rfl⟩ := hf b
    exact ⟨x, y, rfl, rfl, (map_iff f hf (T' i) (hπT' i) x y).mp hab⟩
  apply cong_ext
  intro x y
  constructor
  · intro hxy
    apply hxy (Congruence.comap f (higherComm S))
    intro b
    cases b
    · exact fun u v huv => by
        show (higherComm S).r (f u) (f v)
        rw [show f u = f v from huv]
    · have hCS : CentralAt S (Fin.last (k + 1)) (higherComm S) :=
        (HigherComm.centralAt_iff_le m hmN S _ _).mpr (le_refl' _)
      have h1 := central_comap f T' S hTS _ _ hCS
      have h2 : CentralAt T (Fin.last (k + 1)) (Congruence.comap f (higherComm S)) :=
        centralAt_mono (fun j u v huv => le_sup_left' (T j) (Congruence.ker f) u v huv) h1
      exact (HigherComm.centralAt_iff_le m hm T _ _).mp h2
  · intro hxy
    have hA : ∀ u v, f u = f v → ((higherComm T).sup (Congruence.ker f)).r u v :=
      fun u v h => le_sup_right' _ _ u v h
    have h1 : higherComm T' ≤ (higherComm T).sup (Congruence.ker f) :=
      enlarge_all m hm T _ _ (fun u v h => hA u v h) (le_sup_left' _ _)
    have h2 := (HigherComm.centralAt_iff_le m hm T' (Fin.last (k + 1)) _).mpr h1
    have h3 := central_map f hf T' S hST _ _ hA h2
    have h4 := (HigherComm.centralAt_iff_le m hmN S _ _).mp h3
    exact (map_iff f hf _ hA x y).mp (h4 _ _ hxy)

end Hom

end HCHom
end HigherComm

open HigherComm.HCHom

theorem solution {L : FirstOrder.Language.{u₁, v₁}} {M : Type w₁} [L.Structure M]
    [L.IsAlgebraic] {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4))
    (hm : HigherComm.IsDayTerms M m) {N : Type x₁} [L.Structure N] (f : M →[L] N)
    (hf : Function.Surjective f) (T : Fin (k + 2) → HigherComm.Congruence (L := L) M) :
    (HigherComm.higherComm T).sup (HigherComm.Congruence.ker f) =
      HigherComm.Congruence.comap f
        (HigherComm.higherComm (fun i => HigherComm.Congruence.map f
          ((T i).sup (HigherComm.Congruence.ker f)))) :=
  hom_main m hm f hf T
