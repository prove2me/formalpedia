-- Prove2me | solution 1 for M4aHerbrand.adeleBaseChange_local_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/61dd5c4a-8967-526e-b134-1856bdf284dd

import Mathlib
import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_NumberField_Completion_HenselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_adeleBaseChange_local_rigidity

set_option autoImplicit false

section Fold_RigidityIdempotents

namespace M4aHerbrand
p2m_export "M4aHerbrand" "AdeleBaseChange"
namespace Rigidity
p2m_open "M4aHerbrand"

variable {A : Type*} [CommRing A]

def IsMinIdempotent (e : A) : Prop :=
  IsIdempotentElem e ∧ e ≠ 0 ∧ ∀ f : A, IsIdempotentElem f → f * e = f → f ≠ 0 → f = e

theorem IsMinIdempotent.map_ringEquiv {B : Type*} [CommRing B] (φ : A ≃+* B) {e : A}
    (he : IsMinIdempotent e) : IsMinIdempotent (φ e) := by
  obtain ⟨hid, hne, hmin⟩ := he
  refine ⟨?_, ?_, ?_⟩
  · show φ e * φ e = φ e
    rw [← map_mul, hid.eq]
  · intro h
    exact hne (by simpa using congrArg φ.symm h)
  · intro f hf hfe hfne
    have hf' : IsIdempotentElem (φ.symm f) := by
      show φ.symm f * φ.symm f = φ.symm f
      rw [← map_mul, hf.eq]
    have hfe' : φ.symm f * e = φ.symm f := by
      apply φ.injective
      rw [map_mul, RingEquiv.apply_symm_apply, hfe]
    have hfne' : φ.symm f ≠ 0 := fun h => hfne (by simpa using congrArg φ h)
    have := hmin (φ.symm f) hf' hfe' hfne'
    simpa using congrArg φ this

section Coordinates

variable {ι : Type*} {K : ι → Type*} [∀ i, CommRing (K i)] [∀ i, NoZeroDivisors (K i)]
  (ev : ∀ i, A →+* K i) (hev : ∀ a b : A, (∀ i, ev i a = ev i b) → a = b)
  (δ : ι → A) (hδ₁ : ∀ i, ev i (δ i) = 1) (hδ₀ : ∀ i j, j ≠ i → ev j (δ i) = 0)

omit [∀ i, NoZeroDivisors (K i)] in
include hev in
theorem eq_zero_of_coord (a : A) (h : ∀ i, ev i a = 0) : a = 0 :=
  hev a 0 fun i => by rw [h i, map_zero]

theorem coord_idempotent {e : A} (he : IsIdempotentElem e) (i : ι) : ev i e = 0 ∨ ev i e = 1 := by
  have h : ev i e * (ev i e - 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, he.eq, sub_self]
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

omit [∀ i, NoZeroDivisors (K i)] in
include hδ₁ hδ₀ in
theorem coord_delta [DecidableEq ι] (i j : ι) : ev j (δ i) = if j = i then 1 else 0 := by
  split_ifs with h
  · rw [h]; exact hδ₁ i
  · exact hδ₀ i j h

omit [∀ i, NoZeroDivisors (K i)] in
include hev hδ₁ hδ₀ in
theorem isIdempotentElem_delta (i : ι) : IsIdempotentElem (δ i) := by
  classical
  show δ i * δ i = δ i
  apply hev; intro j
  rw [map_mul, coord_delta ev δ hδ₁ hδ₀]
  split_ifs <;> simp

omit [∀ i, NoZeroDivisors (K i)] in
include hδ₁ in
theorem delta_ne_zero [∀ i, Nontrivial (K i)] (i : ι) : δ i ≠ 0 := by
  intro h
  have := hδ₁ i
  rw [h, map_zero] at this
  exact zero_ne_one this

include hev hδ₁ hδ₀ in

theorem eq_delta_of_mul_delta {f : A} (hf : IsIdempotentElem f) (i : ι) (hfe : f * δ i = f)
    (hfne : f ≠ 0) : f = δ i := by
  classical

  have hoff : ∀ j, j ≠ i → ev j f = 0 := by
    intro j hj
    have := congrArg (ev j) hfe
    rw [map_mul, coord_delta ev δ hδ₁ hδ₀, if_neg hj, mul_zero] at this
    exact this.symm
  rcases coord_idempotent ev hf i with h0 | h1
  · exact absurd (eq_zero_of_coord ev hev f fun j => by
      by_cases hj : j = i
      · subst hj; exact h0
      · exact hoff j hj) hfne
  · apply hev; intro j
    rw [coord_delta ev δ hδ₁ hδ₀]
    split_ifs with hj
    · subst hj; exact h1
    · exact hoff j hj

include hev hδ₁ hδ₀ in
theorem isMinIdempotent_delta [∀ i, Nontrivial (K i)] (i : ι) : IsMinIdempotent (δ i) :=
  ⟨isIdempotentElem_delta ev hev δ hδ₁ hδ₀ i, delta_ne_zero ev δ hδ₁ i,
    fun _ hf hfe hfne => eq_delta_of_mul_delta ev hev δ hδ₁ hδ₀ hf i hfe hfne⟩

omit [∀ i, NoZeroDivisors (K i)] in
include hev hδ₁ hδ₀ in

theorem delta_mul_eq_delta_of_coord_eq_one {e : A} (i : ι) (hi : ev i e = 1) :
    δ i * e = δ i := by
  classical
  apply hev; intro j
  rw [map_mul, coord_delta ev δ hδ₁ hδ₀]
  split_ifs with hj
  · subst hj; rw [hi, one_mul]
  · rw [zero_mul]

include hev hδ₁ hδ₀ in

theorem exists_eq_delta_of_isMinIdempotent [∀ i, Nontrivial (K i)] {e : A} (he : IsMinIdempotent e) :
    ∃ i, e = δ i := by
  obtain ⟨hid, hne, hmin⟩ := he

  have : ∃ i, ev i e ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (eq_zero_of_coord ev hev e h)
  obtain ⟨i, hi⟩ := this
  have hi1 : ev i e = 1 := (coord_idempotent ev hid i).resolve_left hi
  refine ⟨i, ?_⟩

  exact (hmin (δ i) (isIdempotentElem_delta ev hev δ hδ₁ hδ₀ i)
    (delta_mul_eq_delta_of_coord_eq_one ev hev δ hδ₁ hδ₀ i hi1) (delta_ne_zero ev δ hδ₁ i)).symm

include hev hδ₁ hδ₀ in

theorem exists_ringEquiv_delta_eq_delta [∀ i, Nontrivial (K i)] (φ : A ≃+* A) (i : ι) :
    ∃ j, φ (δ i) = δ j :=
  exists_eq_delta_of_isMinIdempotent ev hev δ hδ₁ hδ₀
    ((isMinIdempotent_delta ev hev δ hδ₁ hδ₀ i).map_ringEquiv φ)

omit [∀ i, NoZeroDivisors (K i)] in
include hδ₁ hδ₀ in

theorem delta_injective [∀ i, Nontrivial (K i)] : Function.Injective δ := by
  intro i j h
  by_contra hij
  have := hδ₀ j i hij
  rw [← h, hδ₁ i] at this
  exact one_ne_zero this

end Coordinates

end M4aHerbrand.Rigidity

end Fold_RigidityIdempotents

section Fold_AdeleIndicators

namespace M4aHerbrand
p2m_export "M4aHerbrand" "AdeleBaseChange"
namespace Rigidity
p2m_open "M4aHerbrand"

section FamilyFree

variable {A : Type*} [CommRing A] {ι : Type*} (δ : ι → A)
  (hid : ∀ i, IsIdempotentElem (δ i)) (hne : ∀ i, δ i ≠ 0)
  (hfaith : ∀ a : A, (∀ i, a * δ i = 0) → a = 0)
  (hcorner : ∀ (e : A), IsIdempotentElem e → ∀ i, e * δ i = 0 ∨ e * δ i = δ i)

include hid hne hcorner in
theorem isMinIdempotent_of_corner (i : ι) : IsMinIdempotent (δ i) := by
  refine ⟨hid i, hne i, fun f hf hfe hfne => ?_⟩
  rcases hcorner f hf i with h0 | h1
  · exact absurd (hfe ▸ h0) hfne
  · exact hfe ▸ h1

include hid hfaith hcorner in
theorem exists_eq_delta_of_isMinIdempotent' {e : A} (he : IsMinIdempotent e) : ∃ i, e = δ i := by
  obtain ⟨heid, hene, hmin⟩ := he
  have : ∃ i, e * δ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hene (hfaith e h)
  obtain ⟨i, hi⟩ := this
  have h1 : e * δ i = δ i := (hcorner e heid i).resolve_left hi

  have hne' : δ i ≠ 0 := fun h => hi (by rw [h, mul_zero])
  refine ⟨i, (hmin (δ i) (hid i) ?_ hne').symm⟩
  rw [mul_comm]; exact h1

include hid hne hfaith hcorner in

theorem exists_ringEquiv_delta_eq_delta' (φ : A ≃+* A) (i : ι) : ∃ j, φ (δ i) = δ j :=
  exists_eq_delta_of_isMinIdempotent' δ hid hfaith hcorner
    ((isMinIdempotent_of_corner δ hid hne hcorner i).map_ringEquiv φ)

end FamilyFree

section Adele

open NumberField IsDedekindDomain

variable (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

abbrev PlaceIndex := InfinitePlace F ⊕ HeightOneSpectrum R

theorem adele_fst_mul (x y : AdeleRing R F) : (x * y).1 = x.1 * y.1 := rfl
theorem adele_snd_mul (x y : AdeleRing R F) : (x * y).2 = x.2 * y.2 := rfl
theorem adele_fst_zero : (0 : AdeleRing R F).1 = 0 := rfl
theorem adele_snd_zero : (0 : AdeleRing R F).2 = 0 := rfl
theorem infAdele_mul_apply (x y : InfiniteAdeleRing F) (v : InfinitePlace F) : (x * y) v = x v * y v := rfl
theorem infAdele_zero_apply (v : InfinitePlace F) : (0 : InfiniteAdeleRing F) v = 0 := rfl
theorem finiteAdele_mul_apply (a b : FiniteAdeleRing R F) (v : HeightOneSpectrum R) :
    (a * b) v = a v * b v := rfl
theorem finiteAdele_zero_apply (v : HeightOneSpectrum R) : (0 : FiniteAdeleRing R F) v = 0 := rfl

noncomputable def finiteIndicator [DecidableEq (HeightOneSpectrum R)] (w : HeightOneSpectrum R) :
    FiniteAdeleRing R F :=
  ⟨Pi.single w 1, Filter.Eventually.of_forall fun v => by
    by_cases h : v = w
    · subst h; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _⟩

theorem finiteIndicator_apply [DecidableEq (HeightOneSpectrum R)] (w v : HeightOneSpectrum R) :
    finiteIndicator R F w v = Pi.single (M := fun u => u.adicCompletion F) w 1 v := rfl

theorem finiteIndicator_apply_same [DecidableEq (HeightOneSpectrum R)] (w : HeightOneSpectrum R) :
    finiteIndicator R F w w = 1 := by
  rw [finiteIndicator_apply, Pi.single_eq_same]

theorem finiteIndicator_apply_ne [DecidableEq (HeightOneSpectrum R)] {w v : HeightOneSpectrum R}
    (h : v ≠ w) : finiteIndicator R F w v = 0 := by
  rw [finiteIndicator_apply, Pi.single_eq_of_ne h]

noncomputable def indicator [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum R)] :
    PlaceIndex R F → AdeleRing R F
  | Sum.inl v => (Pi.single v 1, 0)
  | Sum.inr w => (0, finiteIndicator R F w)

variable [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum R)]

theorem indicator_inl_fst (v : InfinitePlace F) : (indicator R F (Sum.inl v)).1 = Pi.single v 1 := rfl
theorem indicator_inl_snd (v : InfinitePlace F) : (indicator R F (Sum.inl v)).2 = 0 := rfl
theorem indicator_inr_fst (w : HeightOneSpectrum R) : (indicator R F (Sum.inr w)).1 = 0 := rfl
theorem indicator_inr_snd (w : HeightOneSpectrum R) : (indicator R F (Sum.inr w)).2 = finiteIndicator R F w :=
  rfl

theorem indicator_inl_fst_same (v : InfinitePlace F) : (indicator R F (Sum.inl v)).1 v = 1 := by
  rw [indicator_inl_fst, Pi.single_eq_same]
theorem indicator_inl_fst_ne {v u : InfinitePlace F} (h : u ≠ v) : (indicator R F (Sum.inl v)).1 u = 0 := by
  rw [indicator_inl_fst, Pi.single_eq_of_ne h]

omit [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum R)] in

theorem adele_ext {x y : AdeleRing R F} (h₁ : ∀ v : InfinitePlace F, x.1 v = y.1 v)
    (h₂ : ∀ w : HeightOneSpectrum R, x.2 w = y.2 w) : x = y :=
  Prod.ext (funext h₁) (FiniteAdeleRing.ext F h₂)

theorem isIdempotentElem_indicator (P : PlaceIndex R F) : IsIdempotentElem (indicator R F P) := by
  rcases P with v | w
  · show indicator R F (Sum.inl v) * indicator R F (Sum.inl v) = indicator R F (Sum.inl v)
    refine adele_ext R F (fun u => ?_) (fun u => ?_)
    · rw [adele_fst_mul, infAdele_mul_apply]
      by_cases h : u = v
      · subst h; rw [indicator_inl_fst_same, mul_one]
      · rw [indicator_inl_fst_ne R F h, mul_zero]
    · rw [adele_snd_mul, indicator_inl_snd, mul_zero]
  · show indicator R F (Sum.inr w) * indicator R F (Sum.inr w) = indicator R F (Sum.inr w)
    refine adele_ext R F (fun u => ?_) (fun u => ?_)
    · rw [adele_fst_mul, indicator_inr_fst, mul_zero]
    · rw [adele_snd_mul, finiteAdele_mul_apply, indicator_inr_snd]
      by_cases h : u = w
      · subst h; rw [finiteIndicator_apply_same, mul_one]
      · rw [finiteIndicator_apply_ne R F h, mul_zero]

theorem indicator_ne_zero (P : PlaceIndex R F) : indicator R F P ≠ 0 := by
  rcases P with v | w
  · intro h
    have h1 := congrArg (fun x : AdeleRing R F => x.1 v) h
    rw [indicator_inl_fst_same, adele_fst_zero, infAdele_zero_apply] at h1
    exact one_ne_zero h1
  · intro h
    have h1 := congrArg (fun x : AdeleRing R F => x.2 w) h
    rw [indicator_inr_snd, finiteIndicator_apply_same, adele_snd_zero, finiteAdele_zero_apply] at h1
    exact one_ne_zero h1

theorem faithful_indicator (a : AdeleRing R F) (h : ∀ P, a * indicator R F P = 0) : a = 0 := by
  refine adele_ext R F (fun v => ?_) (fun w => ?_)
  · have h1 := congrArg (fun x : AdeleRing R F => x.1 v) (h (Sum.inl v))
    rw [adele_fst_mul, infAdele_mul_apply, indicator_inl_fst_same, mul_one, adele_fst_zero,
      infAdele_zero_apply] at h1
    rw [h1, adele_fst_zero, infAdele_zero_apply]
  · have h1 := congrArg (fun x : AdeleRing R F => x.2 w) (h (Sum.inr w))
    rw [adele_snd_mul, finiteAdele_mul_apply, indicator_inr_snd, finiteIndicator_apply_same, mul_one,
      adele_snd_zero, finiteAdele_zero_apply] at h1
    rw [h1, adele_snd_zero, finiteAdele_zero_apply]

theorem eq_zero_or_one_of_mul_self {K : Type*} [Ring K] [NoZeroDivisors K] {x : K} (hx : x * x = x) :
    x = 0 ∨ x = 1 := by
  have h : x * (x - 1) = 0 := by rw [mul_sub, mul_one, hx, sub_self]
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

theorem corner_indicator (e : AdeleRing R F) (he : IsIdempotentElem e) (P : PlaceIndex R F) :
    e * indicator R F P = 0 ∨ e * indicator R F P = indicator R F P := by
  rcases P with v | w
  · have hev : e.1 v * e.1 v = e.1 v := by
      have h1 := congrArg (fun x : AdeleRing R F => x.1 v) he.eq
      rwa [adele_fst_mul, infAdele_mul_apply] at h1
    rcases eq_zero_or_one_of_mul_self hev with h0 | h1
    · left
      refine adele_ext R F (fun u => ?_) (fun u => ?_)
      · rw [adele_fst_mul, infAdele_mul_apply, adele_fst_zero, infAdele_zero_apply]
        by_cases hu : u = v
        · subst hu; rw [h0, zero_mul]
        · rw [indicator_inl_fst_ne R F hu, mul_zero]
      · rw [adele_snd_mul, indicator_inl_snd, mul_zero, adele_snd_zero]
    · right
      refine adele_ext R F (fun u => ?_) (fun u => ?_)
      · rw [adele_fst_mul, infAdele_mul_apply]
        by_cases hu : u = v
        · subst hu; rw [h1, one_mul]
        · rw [indicator_inl_fst_ne R F hu, mul_zero]
      · rw [adele_snd_mul, indicator_inl_snd, mul_zero]
  · have hev : e.2 w * e.2 w = e.2 w := by
      have h1 := congrArg (fun x : AdeleRing R F => x.2 w) he.eq
      rwa [adele_snd_mul, finiteAdele_mul_apply] at h1
    rcases eq_zero_or_one_of_mul_self hev with h0 | h1
    · left
      refine adele_ext R F (fun u => ?_) (fun u => ?_)
      · rw [adele_fst_mul, indicator_inr_fst, mul_zero, adele_fst_zero]
      · rw [adele_snd_mul, finiteAdele_mul_apply, indicator_inr_snd, adele_snd_zero, finiteAdele_zero_apply]
        by_cases hu : u = w
        · subst hu; rw [h0, zero_mul]
        · rw [finiteIndicator_apply_ne R F hu, mul_zero]
    · right
      refine adele_ext R F (fun u => ?_) (fun u => ?_)
      · rw [adele_fst_mul, indicator_inr_fst, mul_zero]
      · rw [adele_snd_mul, finiteAdele_mul_apply, indicator_inr_snd]
        by_cases hu : u = w
        · subst hu; rw [h1, one_mul]
        · rw [finiteIndicator_apply_ne R F hu, mul_zero]

theorem AdeleRing.exists_ringEquiv_indicator_eq (φ : AdeleRing R F ≃+* AdeleRing R F) (P : PlaceIndex R F) :
    ∃ Q, φ (indicator R F P) = indicator R F Q :=
  exists_ringEquiv_delta_eq_delta' (indicator R F) (isIdempotentElem_indicator R F) (indicator_ne_zero R F)
    (faithful_indicator R F) (corner_indicator R F) φ P

end Adele

end M4aHerbrand.Rigidity

end Fold_AdeleIndicators

section Fold_AdeleCorners

namespace M4aHerbrand
p2m_export "M4aHerbrand" "AdeleBaseChange"
namespace Rigidity
p2m_open "M4aHerbrand"

open NumberField IsDedekindDomain

section Corners

variable (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

noncomputable def evalInf (v : InfinitePlace F) : AdeleRing R F →+* v.Completion where
  toFun a := a.1 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable def evalFin (w : HeightOneSpectrum R) : AdeleRing R F →+* w.adicCompletion F where
  toFun a := a.2 w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evalInf_apply (v : InfinitePlace F) (a : AdeleRing R F) : evalInf R F v a = a.1 v := rfl
theorem evalFin_apply (w : HeightOneSpectrum R) (a : AdeleRing R F) : evalFin R F w a = a.2 w := rfl

theorem continuous_evalInf (v : InfinitePlace F) : Continuous (evalInf R F v) := by
  have h1 : Continuous (fun a : InfiniteAdeleRing F × FiniteAdeleRing R F => a.1) := continuous_fst
  have h2 : Continuous (fun b : (InfiniteAdeleRing F) => b v) :=
    continuous_apply (A := fun u : InfinitePlace F => u.Completion) v
  exact h2.comp h1

theorem continuous_evalFin (w : HeightOneSpectrum R) : Continuous (evalFin R F w) := by
  have h1 : Continuous (fun a : InfiniteAdeleRing F × FiniteAdeleRing R F => a.2) := continuous_snd
  have h2 : Continuous (fun b : FiniteAdeleRing R F => b w) :=
    RestrictedProduct.continuous_eval (R := fun u : HeightOneSpectrum R => u.adicCompletion F)
      (A := fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) w
  exact h2.comp h1

variable [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum R)]

noncomputable def singleInf (v : InfinitePlace F) (t : v.Completion) : AdeleRing R F := (Pi.single v t, 0)

omit [IsDedekindDomain R] [DecidableEq (HeightOneSpectrum R)] in
theorem cofinite_le_principal_compl (w : HeightOneSpectrum R) :
    (Filter.cofinite : Filter (HeightOneSpectrum R)) ≤ Filter.principal ({w}ᶜ) :=
  Filter.le_principal_iff.mpr (Set.finite_singleton w).compl_mem_cofinite

noncomputable def singleFinStratum (w : HeightOneSpectrum R) (t : w.adicCompletion F) :
    RestrictedProduct (fun u : HeightOneSpectrum R => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (Filter.principal ({w}ᶜ)) :=
  ⟨Pi.single w t, by
    rw [Filter.eventually_principal]
    intro u hu
    rw [Pi.single_eq_of_ne (by simpa using hu)]
    exact zero_mem _⟩

noncomputable def singleFin (w : HeightOneSpectrum R) (t : w.adicCompletion F) : AdeleRing R F :=
  (0, RestrictedProduct.inclusion _ _ (cofinite_le_principal_compl R w) (singleFinStratum R F w t))

omit [DecidableEq (HeightOneSpectrum R)] in
theorem singleInf_fst (v : InfinitePlace F) (t : v.Completion) : (singleInf R F v t).1 = Pi.single v t := rfl
omit [DecidableEq (HeightOneSpectrum R)] in
theorem singleInf_snd (v : InfinitePlace F) (t : v.Completion) : (singleInf R F v t).2 = 0 := rfl
omit [DecidableEq (InfinitePlace F)] in
theorem singleFin_fst (w : HeightOneSpectrum R) (t : w.adicCompletion F) : (singleFin R F w t).1 = 0 := rfl
omit [DecidableEq (InfinitePlace F)] in
theorem singleFin_snd_apply (w u : HeightOneSpectrum R) (t : w.adicCompletion F) :
    (singleFin R F w t).2 u = Pi.single (M := fun u => u.adicCompletion F) w t u := rfl

omit [DecidableEq (HeightOneSpectrum R)] in
theorem continuous_singleInf (v : InfinitePlace F) : Continuous (singleInf R F v) := by
  have h1 : Continuous (fun t : v.Completion => (Pi.single v t : (u : InfinitePlace F) → u.Completion)) :=
    continuous_single v
  have h2 : Continuous (fun t : v.Completion =>
      ((Pi.single v t : (u : InfinitePlace F) → u.Completion), (0 : FiniteAdeleRing R F))) :=
    h1.prodMk continuous_const
  exact h2

omit [DecidableEq (InfinitePlace F)] in
theorem continuous_singleFin (w : HeightOneSpectrum R) : Continuous (singleFin R F w) := by
  have h0 : Continuous (singleFinStratum R F w) := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_single w
  have h1 : Continuous (fun t => RestrictedProduct.inclusion _ _ (cofinite_le_principal_compl R w)
      (singleFinStratum R F w t)) :=
    (RestrictedProduct.continuous_inclusion (cofinite_le_principal_compl R w)).comp h0
  have h2 : Continuous (fun t : w.adicCompletion F => ((0 : InfiniteAdeleRing F),
      RestrictedProduct.inclusion _ _ (cofinite_le_principal_compl R w) (singleFinStratum R F w t))) :=
    continuous_const.prodMk h1
  exact h2

theorem mul_indicator_inl (a : AdeleRing R F) (v : InfinitePlace F) :
    a * indicator R F (Sum.inl v) = singleInf R F v (evalInf R F v a) := by
  refine adele_ext R F (fun u => ?_) (fun u => ?_)
  · rw [adele_fst_mul, infAdele_mul_apply, singleInf_fst, evalInf_apply]
    by_cases hu : u = v
    · subst hu; rw [indicator_inl_fst_same, mul_one, Pi.single_eq_same]
    · rw [indicator_inl_fst_ne R F hu, mul_zero, Pi.single_eq_of_ne hu]
  · rw [adele_snd_mul, indicator_inl_snd, mul_zero, singleInf_snd]

theorem mul_indicator_inr (a : AdeleRing R F) (w : HeightOneSpectrum R) :
    a * indicator R F (Sum.inr w) = singleFin R F w (evalFin R F w a) := by
  refine adele_ext R F (fun u => ?_) (fun u => ?_)
  · rw [adele_fst_mul, indicator_inr_fst, mul_zero, singleFin_fst]
  · rw [adele_snd_mul, finiteAdele_mul_apply, indicator_inr_snd, singleFin_snd_apply, evalFin_apply]
    by_cases hu : u = w
    · subst hu; rw [finiteIndicator_apply_same, mul_one, Pi.single_eq_same]
    · rw [finiteIndicator_apply_ne R F hu, mul_zero, Pi.single_eq_of_ne hu]

omit [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum R)] in
theorem evalInf_algebraMap (v : InfinitePlace F) (x : F) :
    evalInf R F v (algebraMap F (AdeleRing R F) x) = (x : v.Completion) := rfl

omit [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum R)] in
theorem evalFin_algebraMap (w : HeightOneSpectrum R) (x : F) :
    evalFin R F w (algebraMap F (AdeleRing R F) x) = (x : w.adicCompletion F) := rfl

omit [DecidableEq (HeightOneSpectrum R)] in
theorem evalInf_singleInf (v : InfinitePlace F) (t : v.Completion) : evalInf R F v (singleInf R F v t) = t := by
  rw [evalInf_apply, singleInf_fst, Pi.single_eq_same]

omit [DecidableEq (InfinitePlace F)] in
theorem evalFin_singleFin (w : HeightOneSpectrum R) (t : w.adicCompletion F) :
    evalFin R F w (singleFin R F w t) = t := by
  rw [evalFin_apply, singleFin_snd_apply, Pi.single_eq_same]

theorem singleInf_mul_indicator (v : InfinitePlace F) (t : v.Completion) :
    singleInf R F v t * indicator R F (Sum.inl v) = singleInf R F v t := by
  rw [mul_indicator_inl, evalInf_singleInf]

theorem singleFin_mul_indicator (w : HeightOneSpectrum R) (t : w.adicCompletion F) :
    singleFin R F w t * indicator R F (Sum.inr w) = singleFin R F w t := by
  rw [mul_indicator_inr, evalFin_singleFin]

end Corners

end M4aHerbrand.Rigidity

end Fold_AdeleCorners

section Fold_NonarchRigidity

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3

noncomputable section

namespace M4aHerbrand
p2m_export "M4aHerbrand" "AdeleBaseChange"
namespace LocalRigidity
p2m_open "M4aHerbrand"

open NumberField IsDedekindDomain

section OneCompletion

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem mem_maximalIdeal_iff_valued_lt_one (a : v.adicCompletionIntegers K) :
    a ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔ Valued.v (a : v.adicCompletion K) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have h : Valued.v (a : v.adicCompletion K) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp a.2
  exact ⟨fun hne => lt_of_le_of_ne h hne, fun hlt => ne_of_lt hlt⟩

theorem valued_eq_one_of_sub_one_lt {z : v.adicCompletion K} (hz : Valued.v (z - 1) < 1) : Valued.v z = 1 := by
  have h := Valuation.map_one_add_of_lt (Valued.v) hz
  simpa using h

theorem exists_pow_eq_of_sub_one_lt {z : v.adicCompletion K} (hz : Valued.v (z - 1) < 1)
    {m : ℕ} (hm : Valued.v ((m : ℕ) : v.adicCompletion K) = 1) : ∃ y : v.adicCompletion K, y ^ m = z := by
  have hzO : z ∈ v.adicCompletionIntegers K :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (valued_eq_one_of_sub_one_lt v hz).le
  set z' : v.adicCompletionIntegers K := ⟨z, hzO⟩ with hz'def
  have hz' : z' - 1 ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [mem_maximalIdeal_iff_valued_lt_one]; exact hz
  have hm' : IsUnit ((m : ℕ) : v.adicCompletionIntegers K) := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]; exact hm
  obtain ⟨a, ha, -⟩ := exists_nthRoot_of_sub_one_mem_maximalIdeal hz' hm'
  exact ⟨a, congrArg Subtype.val ha⟩

theorem valued_eq_one_of_frequently_pow {x : v.adicCompletion K} (hx : x ≠ 0)
    (h : ∀ N : ℕ, ∃ m, N ≤ m ∧ ∃ y : v.adicCompletion K, y ^ m = x) : Valued.v x = 1 := by
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  set k : ℤ := WithZero.log (Valued.v x) with hk
  have hxk : Valued.v x = WithZero.exp k := (WithZero.exp_log hvx).symm
  obtain ⟨m, hm, y, rfl⟩ := h (k.natAbs + 1)
  have hvy : Valued.v y ≠ 0 := by
    intro h0
    apply hvx
    rw [Valuation.map_pow, h0, zero_pow (by omega)]
  set j : ℤ := WithZero.log (Valued.v y) with hj
  have hyj : Valued.v y = WithZero.exp j := (WithZero.exp_log hvy).symm
  have hkm : k = m • j := by
    have h1 : Valued.v (y ^ m) = WithZero.exp (m • j) := by
      rw [Valuation.map_pow, hyj, ← WithZero.exp_nsmul]
    rw [hxk] at h1
    exact WithZero.exp_injective h1
  have hj0 : j = 0 := by
    by_contra hne
    have hkabs : (k.natAbs : ℤ) = m * (j.natAbs : ℤ) := by
      rw [Int.natCast_natAbs, Int.natCast_natAbs, hkm, nsmul_eq_mul, abs_mul, Nat.abs_cast]
    have hkabs' : k.natAbs = m * j.natAbs := by exact_mod_cast hkabs
    have hj1 : 1 ≤ j.natAbs := Int.natAbs_pos.mpr hne
    have hmk : m ≤ k.natAbs := hkabs' ▸ Nat.le_mul_of_pos_right m hj1
    omega
  rw [hxk, hkm, hj0, smul_zero, WithZero.exp_zero]

theorem valued_natCast_le_one (n : ℕ) : Valued.v ((n : ℕ) : v.adicCompletion K) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (natCast_mem (v.adicCompletionIntegers K) n)

theorem valued_natCast_eq_one_or (N : ℕ) :
    Valued.v ((N : ℕ) : v.adicCompletion K) = 1 ∨ Valued.v ((N + 1 : ℕ) : v.adicCompletion K) = 1 := by
  by_contra h
  rcases not_or.mp h with ⟨h0, h1⟩
  have h0' : Valued.v ((N : ℕ) : v.adicCompletion K) < 1 := lt_of_le_of_ne (valued_natCast_le_one v N) h0
  have h1' : Valued.v ((N + 1 : ℕ) : v.adicCompletion K) < 1 := lt_of_le_of_ne (valued_natCast_le_one v _) h1
  have h2 : Valued.v (((N + 1 : ℕ) : v.adicCompletion K) - (N : ℕ)) < 1 := Valuation.map_sub_lt _ h1' h0'
  have h3 : ((N + 1 : ℕ) : v.adicCompletion K) - (N : ℕ) = 1 := by push_cast; ring
  rw [h3, Valuation.map_one] at h2
  exact lt_irrefl _ h2

theorem exists_le_valued_natCast_eq_one (N : ℕ) :
    ∃ m, N ≤ m ∧ Valued.v ((m : ℕ) : v.adicCompletion K) = 1 := by
  rcases valued_natCast_eq_one_or v N with h | h
  · exact ⟨N, le_rfl, h⟩
  · exact ⟨N + 1, N.le_succ, h⟩

def teichExp : ℕ := Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) - 1

theorem valued_natCast_teichExp : Valued.v ((teichExp v : ℕ) : v.adicCompletion K) = 1 := by
  classical
  let k := IsLocalRing.ResidueField (v.adicCompletionIntegers K)
  letI : Fintype k := Fintype.ofFinite k
  have hq : (Fintype.card k : k) = 0 := FiniteField.cast_card_eq_zero k
  have hq1 : 1 ≤ Fintype.card k := Fintype.card_pos
  have hcard : teichExp v = Fintype.card k - 1 := by
    simp only [teichExp, k, Nat.card_eq_fintype_card]

  have hunit : IsUnit ((teichExp v : ℕ) : v.adicCompletionIntegers K) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast, hcard, Nat.cast_sub hq1, Nat.cast_one, hq,
      zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hunit
  exact hunit

theorem teichExp_ne_zero : teichExp v ≠ 0 := by
  classical
  let k := IsLocalRing.ResidueField (v.adicCompletionIntegers K)
  letI : Fintype k := Fintype.ofFinite k
  have h2 : 1 < Fintype.card k := Fintype.one_lt_card
  have hcard : teichExp v = Fintype.card k - 1 := by
    simp only [teichExp, k, Nat.card_eq_fintype_card]
  omega

theorem valued_pow_teichExp_sub_one_lt {t : v.adicCompletion K} (ht : Valued.v t = 1) :
    Valued.v (t ^ teichExp v - 1) < 1 := by
  classical
  let k := IsLocalRing.ResidueField (v.adicCompletionIntegers K)
  letI : Fintype k := Fintype.ofFinite k
  have hcard : teichExp v = Fintype.card k - 1 := by
    simp only [teichExp, k, Nat.card_eq_fintype_card]
  have htO : t ∈ v.adicCompletionIntegers K := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ht.le
  obtain ⟨t', rfl⟩ : ∃ t' : v.adicCompletionIntegers K, (t' : v.adicCompletion K) = t := ⟨⟨t, htO⟩, rfl⟩
  have hunit : IsUnit t' := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]; exact ht
  have hres : IsLocalRing.residue _ t' ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hunit
  have hpow : (IsLocalRing.residue _ t') ^ (Fintype.card k - 1) = 1 := FiniteField.pow_card_sub_one_eq_one _ hres
  have hmem : t' ^ teichExp v - 1 ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, map_one, hcard, hpow, sub_self]
  have h := (mem_maximalIdeal_iff_valued_lt_one v _).mp hmem
  push_cast at h
  exact h

theorem eq_one_of_pow_eq_one_of_ne_zero {γ : WithZero (Multiplicative ℤ)} {n : ℕ} (hn : n ≠ 0)
    (h : γ ^ n = 1) : γ = 1 := by
  have h0 : γ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at h
    exact zero_ne_one h
  rw [← WithZero.exp_log h0] at h ⊢
  rw [← WithZero.exp_nsmul, ← WithZero.exp_zero] at h
  have h1 : n • WithZero.log γ = 0 := WithZero.exp_injective h
  rw [nsmul_eq_mul, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd (by exact_mod_cast h1) hn
  · rw [h1, WithZero.exp_zero]

theorem valued_coe_lt_one_iff (x : 𝓞 K) :
    Valued.v ((algebraMap (𝓞 K) K x : K) : v.adicCompletion K) < 1 ↔ x ∈ v.asIdeal := by
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact HeightOneSpectrum.valuation_lt_one_iff_mem v x

theorem valued_coe_eq_one_iff (x : 𝓞 K) :
    Valued.v ((algebraMap (𝓞 K) K x : K) : v.adicCompletion K) = 1 ↔ x ∉ v.asIdeal := by
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact HeightOneSpectrum.valuation_eq_one_iff_notMem v

theorem coe_ne_zero {x : 𝓞 K} (hx : x ≠ 0) : ((algebraMap (𝓞 K) K x : K) : v.adicCompletion K) ≠ 0 := by
  intro h
  have h1 : Valued.v ((algebraMap (𝓞 K) K x : K) : v.adicCompletion K) = 0 := by rw [h, Valuation.map_zero]
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Valuation.zero_iff] at h1
  exact (RingOfIntegers.coe_ne_zero_iff.mpr hx) h1

theorem exists_mem_valued_lt_one :
    ∃ x : 𝓞 K, x ≠ 0 ∧ x ∈ v.asIdeal ∧ Valued.v ((algebraMap (𝓞 K) K x : K) : v.adicCompletion K) < 1 := by
  obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  exact ⟨x, hx0, hxv, (valued_coe_lt_one_iff v x).mpr hxv⟩

theorem exists_eq_mul_of_valued_lt {y c : v.adicCompletion K} (hc : c ≠ 0) (h : Valued.v y < Valued.v c) :
    ∃ y' : v.adicCompletion K, Valued.v y' < 1 ∧ y = c * y' := by
  refine ⟨y * c⁻¹, ?_, ?_⟩
  · rw [Valuation.map_mul, map_inv₀]
    exact mul_inv_lt_of_lt_mul₀ (by rwa [one_mul])
  · rw [mul_left_comm, mul_inv_cancel₀ hc, mul_one]

open WithZeroTopology in

theorem exists_valued_sub_coe_lt (z : v.adicCompletion K) {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0) :
    ∃ x : K, Valued.v (z - (x : v.adicCompletion K)) < γ := by
  have hcont : Continuous (Valued.v : v.adicCompletion K → WithZero (Multiplicative ℤ)) :=
    Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective K)
  have hopen : IsOpen {y : v.adicCompletion K | Valued.v (z - y) < γ} :=
    (WithZeroTopology.isOpen_Iio.preimage hcont).preimage (continuous_const.sub continuous_id)
  obtain ⟨x, hx⟩ := (HeightOneSpectrum.denseRange_algebraMap K v).exists_mem_open hopen
    ⟨z, by simp [pos_iff_ne_zero, hγ]⟩
  exact ⟨x, hx⟩

theorem exists_pow_valued_lt {π : v.adicCompletion K} (hπ0 : Valued.v π ≠ 0) (hπ : Valued.v π < 1)
    {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0) : ∃ k : ℕ, Valued.v π ^ k < γ := by
  set r : ℤ := WithZero.log (Valued.v π) with hr
  have hr' : Valued.v π = WithZero.exp r := (WithZero.exp_log hπ0).symm
  have hrneg : r < 0 := by
    rw [hr', ← WithZero.exp_zero, WithZero.exp_lt_exp] at hπ; exact hπ
  set g : ℤ := WithZero.log γ with hg
  have hg' : γ = WithZero.exp g := (WithZero.exp_log hγ).symm
  refine ⟨g.natAbs + 1, ?_⟩
  rw [hr', hg', ← WithZero.exp_nsmul, WithZero.exp_lt_exp, nsmul_eq_mul]
  have hcast : (((g.natAbs + 1 : ℕ)) : ℤ) = |g| + 1 := by push_cast; ring
  rw [hcast]
  have hr1 : r ≤ -1 := by omega
  have h2 : (0 : ℤ) ≤ |g| + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hr1 h2, neg_abs_le g]

end OneCompletion

section TwoCompletions

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {u : HeightOneSpectrum (𝓞 K)} (w : u.Extension (𝓞 L))
variable (φ : u.adicCompletion K →+* w.1.adicCompletion L)
variable (hφ : ∀ x : K, φ (x : u.adicCompletion K) = ((algebraMap K L x : L) : w.1.adicCompletion L))

theorem mem_under_iff (x : 𝓞 K) : x ∈ u.asIdeal ↔ algebraMap (𝓞 K) (𝓞 L) x ∈ w.1.asIdeal := by
  obtain ⟨w, rfl⟩ := w
  exact Iff.rfl

theorem coe_algebraMap_ringOfIntegers (x : 𝓞 K) :
    ((algebraMap K L (algebraMap (𝓞 K) K x) : L) : w.1.adicCompletion L) =
      ((algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) x) : L) : w.1.adicCompletion L) := by
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem valued_natCast_eq_one_iff (m : ℕ) :
    Valued.v ((m : ℕ) : u.adicCompletion K) = 1 ↔ Valued.v ((m : ℕ) : w.1.adicCompletion L) = 1 := by
  have hK : ((algebraMap (𝓞 K) K (m : 𝓞 K) : K) : u.adicCompletion K) = (m : u.adicCompletion K) := by
    show algebraMap K (u.adicCompletion K) (algebraMap (𝓞 K) K m) = m
    rw [map_natCast, map_natCast]
  have hL : ((algebraMap (𝓞 L) L (m : 𝓞 L) : L) : w.1.adicCompletion L) = (m : w.1.adicCompletion L) := by
    show algebraMap L (w.1.adicCompletion L) (algebraMap (𝓞 L) L m) = m
    rw [map_natCast, map_natCast]
  rw [← hK, ← hL, valued_coe_eq_one_iff, valued_coe_eq_one_iff, mem_under_iff w, map_natCast]

theorem valued_map_eq_one_of_sub_one_lt {z : u.adicCompletion K} (hz : Valued.v (z - 1) < 1) :
    Valued.v (φ z) = 1 := by
  have hz1 := valued_eq_one_of_sub_one_lt u hz
  have hz0 : z ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hz1; exact zero_ne_one hz1
  have hφz0 : φ z ≠ 0 := (map_ne_zero φ).mpr hz0
  refine valued_eq_one_of_frequently_pow w.1 hφz0 fun N => ?_
  obtain ⟨m, hNm, hm⟩ := exists_le_valued_natCast_eq_one u N
  obtain ⟨y, rfl⟩ := exists_pow_eq_of_sub_one_lt u hz hm
  exact ⟨m, hNm, φ y, (map_pow φ y m).symm⟩

theorem valued_map_sub_one_lt {z : u.adicCompletion K} (hz : Valued.v (z - 1) < 1) :
    Valued.v (φ z - 1) < 1 := by

  have hNw : Valued.v ((teichExp w.1 : ℕ) : u.adicCompletion K) = 1 :=
    (valued_natCast_eq_one_iff w _).mpr (valued_natCast_teichExp w.1)
  obtain ⟨y, rfl⟩ := exists_pow_eq_of_sub_one_lt u hz hNw

  have h1 : Valued.v (φ (y ^ teichExp w.1)) = 1 := valued_map_eq_one_of_sub_one_lt w φ hz
  rw [map_pow, Valuation.map_pow] at h1
  have hy : Valued.v (φ y) = 1 := eq_one_of_pow_eq_one_of_ne_zero (teichExp_ne_zero w.1) h1
  rw [map_pow]
  exact valued_pow_teichExp_sub_one_lt w.1 hy

theorem valued_map_lt_one {z : u.adicCompletion K} (hz : Valued.v z < 1) : Valued.v (φ z) < 1 := by
  have h : Valued.v ((1 + z) - 1) < 1 := by rwa [add_sub_cancel_left]
  have h1 := valued_map_sub_one_lt w φ h
  rwa [map_add, map_one, add_sub_cancel_left] at h1

theorem valued_map_le_one {z : u.adicCompletion K} (hz : Valued.v z ≤ 1) : Valued.v (φ z) ≤ 1 := by
  rcases hz.lt_or_eq with hlt | heq
  · exact (valued_map_lt_one w φ hlt).le
  ·
    have h1 := valued_map_eq_one_of_sub_one_lt w φ (valued_pow_teichExp_sub_one_lt u heq)
    rw [map_pow, Valuation.map_pow] at h1
    exact (eq_one_of_pow_eq_one_of_ne_zero (teichExp_ne_zero u) h1).le

include hφ in

theorem valued_map_lt_pow (π : 𝓞 K) (hπ0 : π ≠ 0) (k : ℕ) {y : u.adicCompletion K}
    (hy : Valued.v y < Valued.v ((algebraMap (𝓞 K) K π : K) : u.adicCompletion K) ^ k) :
    Valued.v (φ y) < Valued.v (((algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) π) : L) : w.1.adicCompletion L)) ^ k := by
  set πu : u.adicCompletion K := ((algebraMap (𝓞 K) K π : K) : u.adicCompletion K) with hπudef
  have hπu0 : πu ≠ 0 := coe_ne_zero u hπ0
  rw [← Valuation.map_pow] at hy
  obtain ⟨y', hy', rfl⟩ := exists_eq_mul_of_valued_lt u (pow_ne_zero k hπu0) hy
  have hφπ : φ πu = ((algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) π) : L) : w.1.adicCompletion L) := by
    rw [hπudef, hφ, coe_algebraMap_ringOfIntegers]
  rw [map_mul, map_pow, hφπ, Valuation.map_mul, Valuation.map_pow]
  have hlt := valued_map_lt_one w φ hy'
  have hπw0 : Valued.v (((algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) π) : L) : w.1.adicCompletion L)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (coe_ne_zero w.1
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))).mpr hπ0))
  have hpos : 0 < Valued.v (((algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) π) : L) : w.1.adicCompletion L)) ^ k :=
    zero_lt_iff.mpr (pow_ne_zero k hπw0)
  calc _ < Valued.v (((algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) π) : L) : w.1.adicCompletion L)) ^ k * 1 :=
        mul_lt_mul_of_pos_left hlt hpos
    _ = _ := mul_one _

theorem adicCompletionSemialgHom_compat (x : K) :
    HeightOneSpectrum.Extension.adicCompletionSemialgHom K L w (x : u.adicCompletion K) =
      ((algebraMap K L x : L) : w.1.adicCompletion L) :=
  (HeightOneSpectrum.Extension.adicCompletionSemialgHom K L w).commutes x

include hφ in

theorem eq_adicCompletionSemialgHom (z : u.adicCompletion K) :
    φ z = HeightOneSpectrum.Extension.adicCompletionSemialgHom K L w z := by
  set ι : u.adicCompletion K →+* w.1.adicCompletion L :=
    (HeightOneSpectrum.Extension.adicCompletionSemialgHom K L w : u.adicCompletion K →+* w.1.adicCompletion L)
    with hιdef
  have hι : ∀ x : K, ι (x : u.adicCompletion K) = ((algebraMap K L x : L) : w.1.adicCompletion L) :=
    adicCompletionSemialgHom_compat w
  change φ z = ι z
  by_contra hne
  have hd0 : φ z - ι z ≠ 0 := sub_ne_zero.mpr hne
  have hvd0 : Valued.v (φ z - ι z) ≠ 0 := (Valuation.ne_zero_iff _).mpr hd0

  obtain ⟨π, hπ0, hπu, hπult⟩ := exists_mem_valued_lt_one u
  set πw : w.1.adicCompletion L := ((algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) π) : L) : w.1.adicCompletion L)
    with hπwdef
  have hπw0 : Valued.v πw ≠ 0 := (Valuation.ne_zero_iff _).mpr (coe_ne_zero w.1
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))).mpr hπ0))
  have hπwlt : Valued.v πw < 1 := (valued_coe_lt_one_iff w.1 _).mpr ((mem_under_iff w π).mp hπu)

  obtain ⟨k, hk⟩ := exists_pow_valued_lt w.1 hπw0 hπwlt hvd0

  have hπuk0 : Valued.v ((algebraMap (𝓞 K) K π : K) : u.adicCompletion K) ^ k ≠ 0 :=
    pow_ne_zero k ((Valuation.ne_zero_iff _).mpr (coe_ne_zero u hπ0))
  obtain ⟨x, hx⟩ := exists_valued_sub_coe_lt u z hπuk0

  have h1 : Valued.v (φ (z - x)) < Valued.v πw ^ k := valued_map_lt_pow w φ hφ π hπ0 k hx
  have h2 : Valued.v (ι (z - x)) < Valued.v πw ^ k := valued_map_lt_pow w ι hι π hπ0 k hx
  have heq : φ z - ι z = φ (z - x) - ι (z - x) := by
    rw [map_sub, map_sub, hφ, hι]; ring
  have h3 : Valued.v (φ z - ι z) < Valued.v πw ^ k := by
    rw [heq]; exact Valuation.map_sub_lt _ h1 h2
  exact lt_irrefl _ (h3.trans hk)

include hφ in

theorem coe_eq_adicCompletionSemialgHom :
    (φ : u.adicCompletion K → w.1.adicCompletion L) = HeightOneSpectrum.Extension.adicCompletionSemialgHom K L w :=
  funext (eq_adicCompletionSemialgHom w φ hφ)

include hφ in

theorem continuous_of_compat : Continuous φ := by
  have h : Continuous (φ : u.adicCompletion K → w.1.adicCompletion L) := by
    rw [coe_eq_adicCompletionSemialgHom w φ hφ]
    exact HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous K L w
  exact h

end TwoCompletions

section Exclusions

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem under_eq_of_compat (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (φ : v.adicCompletion K →+* w.adicCompletion L)
    (hφ : ∀ x : K, φ (x : v.adicCompletion K) = ((algebraMap K L x : L) : w.adicCompletion L)) :
    w.under (𝓞 K) = v := by
  by_contra hne

  have hcop : (w.under (𝓞 K)).asIdeal ⊔ v.asIdeal = ⊤ :=
    (w.under (𝓞 K)).isMaximal.coprime_of_ne v.isMaximal
      (fun h => hne (HeightOneSpectrum.ext_iff.mpr h))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hcop)
  set av : v.adicCompletion K := ((algebraMap (𝓞 K) K a : K) : v.adicCompletion K) with havdef
  set bv : v.adicCompletion K := ((algebraMap (𝓞 K) K b : K) : v.adicCompletion K) with hbvdef

  have hab' : av + bv = 1 := by
    show algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) +
      algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K b) = 1
    rw [← map_add, ← map_add, hab, map_one, map_one]
  have ha1 : Valued.v (av - 1) < 1 := by
    have h : av - 1 = -bv := by linear_combination hab'
    rw [h, Valuation.map_neg]
    exact (valued_coe_lt_one_iff v b).mpr hb

  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_add] at hab
    exact v.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr (hab ▸ hb))
  set aw : w.adicCompletion L := ((algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) a) : L) : w.adicCompletion L)
    with hawdef
  have haw0 : aw ≠ 0 :=
    coe_ne_zero w ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))).mpr ha0)
  have hφa : φ av = aw := by
    rw [havdef, hφ, hawdef, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

  have hunit : Valued.v aw = 1 := by
    refine valued_eq_one_of_frequently_pow w haw0 fun N => ?_
    obtain ⟨m, hNm, hm⟩ := exists_le_valued_natCast_eq_one v N
    obtain ⟨y, hy⟩ := exists_pow_eq_of_sub_one_lt v ha1 hm
    exact ⟨m, hNm, φ y, by rw [← map_pow, hy, hφa]⟩

  have haw : algebraMap (𝓞 K) (𝓞 L) a ∈ w.asIdeal := by
    have h : a ∈ (w.under (𝓞 K)).asIdeal := ha
    exact h
  have hlt : Valued.v aw < 1 := (valued_coe_lt_one_iff w _).mpr haw
  rw [hunit] at hlt
  exact lt_irrefl _ hlt

omit [NumberField K] [Algebra K L] in

theorem isEmpty_ringHom_infiniteCompletion_adicCompletion (v : InfinitePlace K) (w : HeightOneSpectrum (𝓞 L)) :
    IsEmpty (v.Completion →+* w.adicCompletion L) := by
  refine ⟨fun φ => ?_⟩

  obtain ⟨r⟩ : Nonempty (ℝ →+* v.Completion) := by
    rcases v.isReal_or_isComplex with hv | hv
    · exact ⟨(InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toRingHom⟩
    · exact ⟨(InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm.toRingHom.comp Complex.ofRealHom⟩
  set ψ : ℝ →+* w.adicCompletion L := φ.comp r with hψ

  set N : ℕ := Ideal.absNorm w.asIdeal with hN
  have hN0 : N ≠ 0 := by
    rw [hN, Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have hNmem : ((N : 𝓞 L)) ∈ w.asIdeal := by rw [hN]; exact Ideal.absNorm_mem w.asIdeal
  have hNlt : Valued.v ((algebraMap (𝓞 L) L (N : 𝓞 L) : L) : w.adicCompletion L) < 1 :=
    (valued_coe_lt_one_iff w _).mpr hNmem
  have hcast : ((algebraMap (𝓞 L) L (N : 𝓞 L) : L) : w.adicCompletion L) = (N : w.adicCompletion L) := by
    show algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L N) = N
    rw [map_natCast, map_natCast]
  rw [hcast] at hNlt
  haveI : CharZero (w.adicCompletion L) := charZero_of_injective_algebraMap (algebraMap L _).injective
  have hNw0 : (N : w.adicCompletion L) ≠ 0 := Nat.cast_ne_zero.mpr hN0

  have hunit : Valued.v (N : w.adicCompletion L) = 1 := by
    refine valued_eq_one_of_frequently_pow w hNw0 fun M => ⟨M + 1, M.le_succ, ?_⟩
    refine ⟨ψ ((N : ℝ) ^ ((M + 1 : ℕ) : ℝ)⁻¹), ?_⟩
    rw [← map_pow, Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) (Nat.succ_ne_zero M), map_natCast]
  rw [hunit] at hNlt
  exact lt_irrefl _ hNlt

theorem not_finite_ringHom_adicCompletion_of_isAlgClosed (v : HeightOneSpectrum (𝓞 K))
    {E : Type*} [Field E] [IsAlgClosed E] (j : v.adicCompletion K →+* E) : ¬ j.Finite := by
  intro hj
  letI : Algebra (v.adicCompletion K) E := j.toAlgebra
  haveI : Module.Finite (v.adicCompletion K) E := hj
  set d : ℕ := Module.finrank (v.adicCompletion K) E with hd
  have hdpos : 0 < d := Module.finrank_pos
  obtain ⟨π, hπ0, -, hπlt⟩ := exists_mem_valued_lt_one v
  set πv : v.adicCompletion K := ((algebraMap (𝓞 K) K π : K) : v.adicCompletion K) with hπvdef
  have hπv0 : πv ≠ 0 := coe_ne_zero v hπ0
  have hunit : Valued.v (πv ^ d) = 1 := by
    refine valued_eq_one_of_frequently_pow v (pow_ne_zero _ hπv0) fun M => ⟨M + 1, M.le_succ, ?_⟩
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap (v.adicCompletion K) E πv) (n := M + 1)
      (Nat.succ_pos M)
    refine ⟨Algebra.norm (v.adicCompletion K) z, ?_⟩
    rw [← map_pow, hz, Algebra.norm_algebraMap]
  rw [Valuation.map_pow] at hunit
  have h1 : Valued.v πv = 1 := eq_one_of_pow_eq_one_of_ne_zero hdpos.ne' hunit
  rw [h1] at hπlt
  exact lt_irrefl _ hπlt

omit [NumberField L] in

private theorem _root_.M4aHerbrand.LocalRigidity.finite_extensionEmbedding (w : InfinitePlace L) :
    (InfinitePlace.Completion.extensionEmbedding w).Finite := by
  rcases w.isReal_or_isComplex with hw | hw
  · have h1 : InfinitePlace.Completion.extensionEmbedding w =
        (algebraMap ℝ ℂ).comp (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw) := by
      ext x
      exact (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw x).symm
    rw [h1]
    exact RingHom.Finite.comp (RingHom.finite_algebraMap.mpr inferInstance)
      (RingHom.Finite.of_surjective _ (InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hw))
  · exact RingHom.Finite.of_surjective _ (InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw)

p2m_export "M4aHerbrand.LocalRigidity" "finite_extensionEmbedding"
omit [NumberField L] [Algebra K L] in

theorem not_finite_ringHom_adicCompletion_infiniteCompletion (v : HeightOneSpectrum (𝓞 K))
    (w : InfinitePlace L) (φ : v.adicCompletion K →+* w.Completion) : ¬ φ.Finite := fun hφ =>
  not_finite_ringHom_adicCompletion_of_isAlgClosed v
    ((InfinitePlace.Completion.extensionEmbedding w).comp φ) ((finite_extensionEmbedding w).comp hφ)

end Exclusions

end M4aHerbrand.LocalRigidity

end

end Fold_NonarchRigidity

section Fold_BaseChangeCorners

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain

namespace M4aHerbrand
p2m_export "M4aHerbrand" "AdeleBaseChange"
namespace Rigidity
p2m_open "M4aHerbrand"

section CornerHom

variable (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

theorem adele_fst_add (x y : AdeleRing R F) : (x + y).1 = x.1 + y.1 := rfl
theorem adele_snd_add (x y : AdeleRing R F) : (x + y).2 = x.2 + y.2 := rfl
theorem infAdele_add_apply (x y : InfiniteAdeleRing F) (v : InfinitePlace F) : (x + y) v = x v + y v := rfl
theorem finiteAdele_add_apply (a b : FiniteAdeleRing R F) (v : HeightOneSpectrum R) : (a + b) v = a v + b v :=
  rfl

variable [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum R)]
variable {T : Type*} [Semiring T]

theorem singleInf_one (v : InfinitePlace F) : singleInf R F v 1 = indicator R F (Sum.inl v) := rfl

omit [DecidableEq (HeightOneSpectrum R)] in
theorem singleInf_mul (v : InfinitePlace F) (s t : v.Completion) :
    singleInf R F v (s * t) = singleInf R F v s * singleInf R F v t := by
  refine adele_ext R F (fun u => ?_) (fun u => ?_)
  · rw [adele_fst_mul, infAdele_mul_apply, singleInf_fst, singleInf_fst, singleInf_fst]
    by_cases hu : u = v
    · subst hu; rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hu, Pi.single_eq_of_ne hu, Pi.single_eq_of_ne hu, mul_zero]
  · rw [adele_snd_mul, finiteAdele_mul_apply, singleInf_snd, singleInf_snd, singleInf_snd, finiteAdele_zero_apply,
      mul_zero]

omit [DecidableEq (HeightOneSpectrum R)] in
theorem singleInf_add (v : InfinitePlace F) (s t : v.Completion) :
    singleInf R F v (s + t) = singleInf R F v s + singleInf R F v t := by
  refine adele_ext R F (fun u => ?_) (fun u => ?_)
  · rw [adele_fst_add, infAdele_add_apply, singleInf_fst, singleInf_fst, singleInf_fst]
    by_cases hu : u = v
    · subst hu; rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hu, Pi.single_eq_of_ne hu, Pi.single_eq_of_ne hu, add_zero]
  · rw [adele_snd_add, finiteAdele_add_apply, singleInf_snd, singleInf_snd, singleInf_snd, finiteAdele_zero_apply,
      add_zero]

omit [DecidableEq (HeightOneSpectrum R)] in
theorem singleInf_map_zero (v : InfinitePlace F) : singleInf R F v 0 = 0 := by
  refine adele_ext R F (fun u => ?_) (fun u => ?_)
  · rw [singleInf_fst, adele_fst_zero, infAdele_zero_apply]
    by_cases hu : u = v
    · subst hu; rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hu]
  · rw [singleInf_snd, adele_snd_zero]

theorem singleFin_one (w : HeightOneSpectrum R) : singleFin R F w 1 = indicator R F (Sum.inr w) := by
  refine adele_ext R F (fun u => ?_) (fun u => ?_)
  · rw [singleFin_fst, indicator_inr_fst]
  · rw [singleFin_snd_apply, indicator_inr_snd, finiteIndicator_apply]

omit [DecidableEq (InfinitePlace F)] in
theorem singleFin_mul (w : HeightOneSpectrum R) (s t : w.adicCompletion F) :
    singleFin R F w (s * t) = singleFin R F w s * singleFin R F w t := by
  refine adele_ext R F (fun u => ?_) (fun u => ?_)
  · rw [adele_fst_mul, infAdele_mul_apply, singleFin_fst, singleFin_fst, singleFin_fst, infAdele_zero_apply,
      mul_zero]
  · rw [adele_snd_mul, finiteAdele_mul_apply, singleFin_snd_apply, singleFin_snd_apply, singleFin_snd_apply]
    by_cases hu : u = w
    · subst hu; rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hu, Pi.single_eq_of_ne hu, Pi.single_eq_of_ne hu, mul_zero]

omit [DecidableEq (InfinitePlace F)] in
theorem singleFin_add (w : HeightOneSpectrum R) (s t : w.adicCompletion F) :
    singleFin R F w (s + t) = singleFin R F w s + singleFin R F w t := by
  refine adele_ext R F (fun u => ?_) (fun u => ?_)
  · rw [adele_fst_add, infAdele_add_apply, singleFin_fst, singleFin_fst, singleFin_fst, infAdele_zero_apply,
      add_zero]
  · rw [adele_snd_add, finiteAdele_add_apply, singleFin_snd_apply, singleFin_snd_apply, singleFin_snd_apply]
    by_cases hu : u = w
    · subst hu; rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hu, Pi.single_eq_of_ne hu, Pi.single_eq_of_ne hu, add_zero]

omit [DecidableEq (InfinitePlace F)] in
theorem singleFin_map_zero (w : HeightOneSpectrum R) : singleFin R F w 0 = 0 := by
  refine adele_ext R F (fun u => ?_) (fun u => ?_)
  · rw [singleFin_fst, adele_fst_zero]
  · rw [singleFin_snd_apply, adele_snd_zero, finiteAdele_zero_apply]
    by_cases hu : u = w
    · subst hu; rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hu]

def cornerHomInf (ψ : AdeleRing R F →+* T) (v : InfinitePlace F) (h : ψ (indicator R F (Sum.inl v)) = 1) :
    v.Completion →+* T where
  toFun t := ψ (singleInf R F v t)
  map_one' := by rw [singleInf_one, h]
  map_mul' s t := by rw [singleInf_mul, map_mul]
  map_zero' := by rw [singleInf_map_zero, map_zero]
  map_add' s t := by rw [singleInf_add, map_add]

theorem cornerHomInf_apply (ψ : AdeleRing R F →+* T) (v : InfinitePlace F) (h) (t : v.Completion) :
    cornerHomInf R F ψ v h t = ψ (singleInf R F v t) := rfl

theorem eq_cornerHomInf (ψ : AdeleRing R F →+* T) (v : InfinitePlace F) (h) (a : AdeleRing R F) :
    ψ a = cornerHomInf R F ψ v h ((a.1 : InfiniteAdeleRing F) v) := by
  rw [cornerHomInf_apply, ← evalInf_apply R F v a, ← mul_indicator_inl, map_mul, h, mul_one]

theorem cornerHomInf_coe (ψ : AdeleRing R F →+* T) (v : InfinitePlace F) (h) (x : F) :
    cornerHomInf R F ψ v h (x : v.Completion) = ψ (algebraMap F (AdeleRing R F) x) := by
  rw [eq_cornerHomInf R F ψ v h (algebraMap F (AdeleRing R F) x)]; rfl

def cornerHomFin (ψ : AdeleRing R F →+* T) (w : HeightOneSpectrum R) (h : ψ (indicator R F (Sum.inr w)) = 1) :
    w.adicCompletion F →+* T where
  toFun t := ψ (singleFin R F w t)
  map_one' := by rw [singleFin_one, h]
  map_mul' s t := by rw [singleFin_mul, map_mul]
  map_zero' := by rw [singleFin_map_zero, map_zero]
  map_add' s t := by rw [singleFin_add, map_add]

theorem cornerHomFin_apply (ψ : AdeleRing R F →+* T) (w : HeightOneSpectrum R) (h) (t : w.adicCompletion F) :
    cornerHomFin R F ψ w h t = ψ (singleFin R F w t) := rfl

theorem eq_cornerHomFin (ψ : AdeleRing R F →+* T) (w : HeightOneSpectrum R) (h) (a : AdeleRing R F) :
    ψ a = cornerHomFin R F ψ w h ((a.2 : FiniteAdeleRing R F) w) := by
  rw [cornerHomFin_apply, ← evalFin_apply R F w a, ← mul_indicator_inr, map_mul, h, mul_one]

theorem cornerHomFin_coe (ψ : AdeleRing R F →+* T) (w : HeightOneSpectrum R) (h) (x : F) :
    cornerHomFin R F ψ w h (x : w.adicCompletion F) = ψ (algebraMap F (AdeleRing R F) x) := by
  rw [eq_cornerHomFin R F ψ w h (algebraMap F (AdeleRing R F) x)]; rfl

end CornerHom

end M4aHerbrand.Rigidity

namespace M4aHerbrand
p2m_export "M4aHerbrand" "AdeleBaseChange"
namespace AdeleBaseChange
p2m_export "M4aHerbrand.AdeleBaseChange" "tensorEquiv β_compat tensorEquiv_one_tmul β"
p2m_open "M4aHerbrand.AdeleBaseChange M4aHerbrand"

open M4aHerbrand.Rigidity

section Datum

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L)

def adeleBasis :
    letI := B.β.toAlgebra
    Module.Basis (Fin (Module.finrank K L)) (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
  letI := B.β.toAlgebra
  (Algebra.TensorProduct.basis (AdeleRing (𝓞 K) K) (Module.finBasis K L)).map B.tensorEquiv.toLinearEquiv

theorem adeleBasis_apply (i : Fin (Module.finrank K L)) :
    (letI := B.β.toAlgebra; adeleBasis B i) = algebraMap L (AdeleRing (𝓞 L) L) (Module.finBasis K L i) := by
  letI := B.β.toAlgebra
  show ((Algebra.TensorProduct.basis (AdeleRing (𝓞 K) K) (Module.finBasis K L)).map
    B.tensorEquiv.toLinearEquiv) i = _
  rw [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, Algebra.TensorProduct.basis_apply]
  exact B.tensorEquiv_one_tmul _

def basisCoord (x : AdeleRing (𝓞 L) L) (i : Fin (Module.finrank K L)) : AdeleRing (𝓞 K) K :=
  letI := B.β.toAlgebra
  (adeleBasis B).repr x i

theorem sum_basisCoord (x : AdeleRing (𝓞 L) L) :
    ∑ i, B.β (basisCoord B x i) * algebraMap L (AdeleRing (𝓞 L) L) (Module.finBasis K L i) = x := by
  letI := B.β.toAlgebra
  conv_rhs => rw [← (adeleBasis B).sum_repr x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [adeleBasis_apply]; rfl

theorem basisCoord_mul (c : AdeleRing (𝓞 K) K) (x : AdeleRing (𝓞 L) L) (i : Fin (Module.finrank K L)) :
    basisCoord B (B.β c * x) i = c * basisCoord B x i := by
  letI := B.β.toAlgebra
  have h : B.β c * x = c • x := rfl
  show (adeleBasis B).repr (B.β c * x) i = c * (adeleBasis B).repr x i
  rw [h, map_smul, Finsupp.smul_apply, smul_eq_mul]

variable [DecidableEq (InfinitePlace K)] [DecidableEq (HeightOneSpectrum (𝓞 K))]

theorem exists_indicator_mul_ne_zero (x : AdeleRing (𝓞 L) L) (hx : x ≠ 0) :
    ∃ P : PlaceIndex (𝓞 K) K, B.β (indicator (𝓞 K) K P) * x ≠ 0 := by
  by_contra h
  apply hx
  have h' : ∀ P : PlaceIndex (𝓞 K) K, B.β (indicator (𝓞 K) K P) * x = 0 := fun P =>
    not_not.mp (not_exists.mp h P)
  have hc : ∀ i, basisCoord B x i = 0 := fun i =>
    faithful_indicator (𝓞 K) K (basisCoord B x i) fun P => by
      rw [mul_comm, ← basisCoord_mul, h' P]
      letI := B.β.toAlgebra
      show (adeleBasis B).repr 0 i = 0
      rw [map_zero, Finsupp.zero_apply]
  rw [← sum_basisCoord B x]
  exact Finset.sum_eq_zero fun i _ => by rw [hc i, map_zero, zero_mul]

variable [DecidableEq (InfinitePlace L)] [DecidableEq (HeightOneSpectrum (𝓞 L))]

theorem exists_indicator_snd_eq_one (w : HeightOneSpectrum (𝓞 L)) :
    ∃ P : PlaceIndex (𝓞 K) K, ((B.β (indicator (𝓞 K) K P)).2 : FiniteAdeleRing (𝓞 L) L) w = 1 := by
  obtain ⟨P, hP⟩ := exists_indicator_mul_ne_zero B (indicator (𝓞 L) L (Sum.inr w)) (indicator_ne_zero _ _ _)
  refine ⟨P, ?_⟩
  rw [mul_indicator_inr] at hP
  have hne : evalFin (𝓞 L) L w (B.β (indicator (𝓞 K) K P)) ≠ 0 := by
    intro h0; apply hP; rw [h0, singleFin_map_zero]
  have hid : IsIdempotentElem (B.β (indicator (𝓞 K) K P)) := (isIdempotentElem_indicator (𝓞 K) K P).map B.β
  rcases eq_zero_or_one_of_mul_self (x := evalFin (𝓞 L) L w (B.β (indicator (𝓞 K) K P)))
      (by rw [← map_mul, hid.eq]) with h | h
  · exact absurd h hne
  · exact h

theorem exists_indicator_fst_eq_one (w : InfinitePlace L) :
    ∃ P : PlaceIndex (𝓞 K) K, ((B.β (indicator (𝓞 K) K P)).1 : InfiniteAdeleRing L) w = 1 := by
  obtain ⟨P, hP⟩ := exists_indicator_mul_ne_zero B (indicator (𝓞 L) L (Sum.inl w)) (indicator_ne_zero _ _ _)
  refine ⟨P, ?_⟩
  rw [mul_indicator_inl] at hP
  have hne : evalInf (𝓞 L) L w (B.β (indicator (𝓞 K) K P)) ≠ 0 := by
    intro h0; apply hP; rw [h0, singleInf_map_zero]
  have hid : IsIdempotentElem (B.β (indicator (𝓞 K) K P)) := (isIdempotentElem_indicator (𝓞 K) K P).map B.β
  rcases eq_zero_or_one_of_mul_self (x := evalInf (𝓞 L) L w (B.β (indicator (𝓞 K) K P)))
      (by rw [← map_mul, hid.eq]) with h | h
  · exact absurd h hne
  · exact h

omit [DecidableEq (InfinitePlace L)] [DecidableEq (HeightOneSpectrum (𝓞 L))] in

theorem finite_cornerHomFin {T : Type*} [CommRing T] (ev : AdeleRing (𝓞 L) L →+* T)
    (sec : T → AdeleRing (𝓞 L) L) (hsec : ∀ t, ev (sec t) = t)
    (v : HeightOneSpectrum (𝓞 K)) (h : (ev.comp B.β) (indicator (𝓞 K) K (Sum.inr v)) = 1) :
    (cornerHomFin (𝓞 K) K (ev.comp B.β) v h).Finite := by
  classical
  letI := (cornerHomFin (𝓞 K) K (ev.comp B.β) v h).toAlgebra
  refine Module.finite_def.mpr ⟨(Finset.univ.image fun i => ev (algebraMap L (AdeleRing (𝓞 L) L)
    (Module.finBasis K L i))), ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, eq_top_iff]
  rintro t -
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun i => ((basisCoord B (sec t) i).2 : FiniteAdeleRing (𝓞 K) K) v, ?_⟩
  conv_rhs => rw [← hsec t, ← sum_basisCoord B (sec t), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Algebra.smul_def]
  congr 1
  exact (eq_cornerHomFin (𝓞 K) K (ev.comp B.β) v h (basisCoord B (sec t) i)).symm

omit [DecidableEq (InfinitePlace L)] [DecidableEq (HeightOneSpectrum (𝓞 L))] in

theorem finite_cornerHomInf {T : Type*} [CommRing T] (ev : AdeleRing (𝓞 L) L →+* T)
    (sec : T → AdeleRing (𝓞 L) L) (hsec : ∀ t, ev (sec t) = t)
    (v : InfinitePlace K) (h : (ev.comp B.β) (indicator (𝓞 K) K (Sum.inl v)) = 1) :
    (cornerHomInf (𝓞 K) K (ev.comp B.β) v h).Finite := by
  classical
  letI := (cornerHomInf (𝓞 K) K (ev.comp B.β) v h).toAlgebra
  refine Module.finite_def.mpr ⟨(Finset.univ.image fun i => ev (algebraMap L (AdeleRing (𝓞 L) L)
    (Module.finBasis K L i))), ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, eq_top_iff]
  rintro t -
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun i => ((basisCoord B (sec t) i).1 : InfiniteAdeleRing K) v, ?_⟩
  conv_rhs => rw [← hsec t, ← sum_basisCoord B (sec t), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Algebra.smul_def]
  congr 1
  exact (eq_cornerHomInf (𝓞 K) K (ev.comp B.β) v h (basisCoord B (sec t) i)).symm

end Datum

section Exports

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L)

theorem exists_arch_corner (w : InfinitePlace L) :
    ∃ (v : InfinitePlace K) (φ : v.Completion →+* w.Completion),
      φ.Finite ∧ (∀ x : K, φ (x : v.Completion) = ((algebraMap K L x : L) : w.Completion)) ∧
      ∀ a : AdeleRing (𝓞 K) K,
        ((B.β a).1 : InfiniteAdeleRing L) w = φ ((a.1 : InfiniteAdeleRing K) v) := by
  classical
  obtain ⟨P, hP⟩ := exists_indicator_fst_eq_one B w
  set ψ : AdeleRing (𝓞 K) K →+* w.Completion := (evalInf (𝓞 L) L w).comp B.β with hψ
  have hψP : ψ (indicator (𝓞 K) K P) = 1 := hP
  have hsec : ∀ t : w.Completion, evalInf (𝓞 L) L w (singleInf (𝓞 L) L w t) = t := evalInf_singleInf (𝓞 L) L w
  rcases P with v | v
  · refine ⟨v, cornerHomInf (𝓞 K) K ψ v hψP, finite_cornerHomInf B _ _ hsec v hψP, fun x => ?_, fun a => ?_⟩
    · rw [cornerHomInf_coe, hψ, RingHom.comp_apply, B.β_compat]; rfl
    · exact eq_cornerHomInf (𝓞 K) K ψ v hψP a
  · exact absurd (finite_cornerHomFin B _ _ hsec v hψP)
      (LocalRigidity.not_finite_ringHom_adicCompletion_infiniteCompletion v w _)

theorem beta_snd_apply_eq (a : AdeleRing (𝓞 K) K) (w : HeightOneSpectrum (𝓞 L)) :
    ((B.β a).2 : FiniteAdeleRing (𝓞 L) L) w =
      HeightOneSpectrum.Extension.adicCompletionSemialgHom K L
        (⟨w, rfl⟩ : (w.under (𝓞 K)).Extension (𝓞 L))
        ((a.2 : FiniteAdeleRing (𝓞 K) K) (w.under (𝓞 K))) := by
  classical
  obtain ⟨P, hP⟩ := exists_indicator_snd_eq_one B w
  set ψ : AdeleRing (𝓞 K) K →+* w.adicCompletion L := (evalFin (𝓞 L) L w).comp B.β with hψ
  have hψP : ψ (indicator (𝓞 K) K P) = 1 := hP
  rcases P with v | v
  · exact ((LocalRigidity.isEmpty_ringHom_infiniteCompletion_adicCompletion v w).false
      (cornerHomInf (𝓞 K) K ψ v hψP)).elim
  · set φ := cornerHomFin (𝓞 K) K ψ v hψP with hφdef
    have hφ : ∀ x : K, φ (x : v.adicCompletion K) = ((algebraMap K L x : L) : w.adicCompletion L) := fun x => by
      rw [hφdef, cornerHomFin_coe, hψ, RingHom.comp_apply, B.β_compat]; rfl
    obtain rfl : w.under (𝓞 K) = v := LocalRigidity.under_eq_of_compat v w φ hφ
    rw [← LocalRigidity.eq_adicCompletionSemialgHom ⟨w, rfl⟩ φ hφ]
    exact eq_cornerHomFin (𝓞 K) K ψ _ hψP a

end Exports

end M4aHerbrand.AdeleBaseChange

namespace M4aHerbrand p2m_export "M4aHerbrand" "AdeleBaseChange" end M4aHerbrand
p2m_open_scoped "M4aHerbrand" in

theorem M4aHerbrand.adeleBaseChange_fin_rigidity
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (B : M4aHerbrand.AdeleBaseChange (𝓞 K) K (𝓞 L) L) :
    ∀ (a : AdeleRing (𝓞 K) K) (w : HeightOneSpectrum (𝓞 L)),
      ((B.β a).2 : FiniteAdeleRing (𝓞 L) L) w =
        HeightOneSpectrum.Extension.adicCompletionSemialgHom K L
          (⟨w, rfl⟩ : (w.under (𝓞 K)).Extension (𝓞 L))
          ((a.2 : FiniteAdeleRing (𝓞 K) K) (w.under (𝓞 K))) :=
  fun a w => M4aHerbrand.AdeleBaseChange.beta_snd_apply_eq B a w

end

end Fold_BaseChangeCorners

section Fold_ArchRigidityCore

set_option autoImplicit false

open NumberField

namespace M4aHerbrand
p2m_export "M4aHerbrand" "AdeleBaseChange"
p2m_open "M4aHerbrand"
namespace ArchRigidityCore

section C2

variable {K : Type*} [Field K]

theorem ofReal_mem_range_extensionEmbedding (v : InfinitePlace K) (r : ℝ) :
    (r : ℂ) ∈ Set.range (InfinitePlace.Completion.extensionEmbedding v) := by
  by_cases hv : v.IsReal
  · obtain ⟨x, hx⟩ := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hv r
    exact ⟨x, by rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv, hx]⟩
  · exact InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex
      (InfinitePlace.not_isReal_iff_isComplex.1 hv) (r : ℂ)

theorem finite_extensionEmbedding (v : InfinitePlace K) :
    (InfinitePlace.Completion.extensionEmbedding v).Finite := by
  letI : Algebra v.Completion ℂ := (InfinitePlace.Completion.extensionEmbedding v).toAlgebra
  have hfin : Module.Finite v.Completion ℂ := by
    refine ⟨Submodule.fg_def.mpr
      ⟨{1, Complex.I}, (Set.finite_singleton Complex.I).insert 1, ?_⟩⟩
    rw [eq_top_iff]
    rintro z -
    obtain ⟨x, hx⟩ := ofReal_mem_range_extensionEmbedding v z.re
    obtain ⟨y, hy⟩ := ofReal_mem_range_extensionEmbedding v z.im
    have hz : z = x • (1 : ℂ) + y • Complex.I := by
      rw [Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra, hx, hy, mul_one]
      exact (Complex.re_add_im z).symm
    rw [hz]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  exact hfin

end C2

section C1

variable {A : Type*} [Field A]

theorem exists_ringEquiv_comp (j₁ j₂ : A →+* ℂ) (h₁ : j₁.Finite) (h₂ : j₂.Finite) :
    ∃ θ : ℂ ≃+* ℂ, ∀ x : A, θ (j₂ x) = j₁ x := by
  haveI htf₁ : (letI := j₁.toAlgebra; Module.IsTorsionFree A ℂ) := by
    letI := j₁.toAlgebra
    exact inferInstance
  haveI htf₂ : (letI := j₂.toAlgebra; Module.IsTorsionFree A ℂ) := by
    letI := j₂.toAlgebra
    exact inferInstance
  haveI hc₁ : @IsAlgClosure A ℂ _ _ j₁.toAlgebra htf₁ := by
    letI := j₁.toAlgebra
    haveI : Module.Finite A ℂ := h₁
    exact ⟨inferInstance, inferInstance⟩
  haveI hc₂ : @IsAlgClosure A ℂ _ _ j₂.toAlgebra htf₂ := by
    letI := j₂.toAlgebra
    haveI : Module.Finite A ℂ := h₂
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨@IsAlgClosure.equivOfEquiv A A ℂ ℂ _ _ _ _ j₁.toAlgebra htf₁ hc₁ j₂.toAlgebra htf₂ hc₂
    _ _ (RingEquiv.refl A), fun x => ?_⟩
  have h := @IsAlgClosure.equivOfEquiv_algebraMap A A ℂ ℂ _ _ _ _ j₁.toAlgebra htf₁ hc₁
    j₂.toAlgebra htf₂ hc₂ _ _ (RingEquiv.refl A) x
  simpa [RingHom.algebraMap_toAlgebra] using h

end C1

end ArchRigidityCore
end M4aHerbrand

end Fold_ArchRigidityCore

section Fold_ArchRigidityAssembly

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace M4aHerbrand
p2m_export "M4aHerbrand" "AdeleBaseChange"
p2m_open "M4aHerbrand"

theorem archRigid_of_corner {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L)
    (hpkg : ∀ w : InfinitePlace L, ∃ (v : InfinitePlace K) (φ : v.Completion →+* w.Completion),
      φ.Finite ∧
      ∀ a : AdeleRing (𝓞 K) K,
        ((B.β a).1 : InfiniteAdeleRing L) w = φ ((a.1 : InfiniteAdeleRing K) v)) :
    ∀ w : InfinitePlace L, ∃ (v : InfinitePlace K) (θ : ℂ ≃+* ℂ), ∀ a : AdeleRing (𝓞 K) K,
      InfinitePlace.Completion.extensionEmbedding w (((B.β a).1 : InfiniteAdeleRing L) w) =
        θ (InfinitePlace.Completion.extensionEmbedding v ((a.1 : InfiniteAdeleRing K) v)) := by
  intro w
  obtain ⟨v, φ, hfin, heq⟩ := hpkg w
  obtain ⟨θ, hθ⟩ := ArchRigidityCore.exists_ringEquiv_comp
    ((InfinitePlace.Completion.extensionEmbedding w).comp φ)
    (InfinitePlace.Completion.extensionEmbedding v)
    ((ArchRigidityCore.finite_extensionEmbedding w).comp hfin)
    (ArchRigidityCore.finite_extensionEmbedding v)
  exact ⟨v, θ, fun a => by rw [heq a]; exact (hθ ((a.1 : InfiniteAdeleRing K) v)).symm⟩

end M4aHerbrand

end Fold_ArchRigidityAssembly

open NumberField IsDedekindDomain _root_.M4aHerbrand _root_.P2MW.S_M4aHerbrand_adeleBaseChange_local_rigidity.M4aHerbrand in

theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) :
    (∀ (a : AdeleRing (𝓞 K) K) (w : HeightOneSpectrum (𝓞 L)),
      ((B.β a).2 : FiniteAdeleRing (𝓞 L) L) w =
        HeightOneSpectrum.Extension.adicCompletionSemialgHom K L
          (⟨w, rfl⟩ : (w.under (𝓞 K)).Extension (𝓞 L))
          ((a.2 : FiniteAdeleRing (𝓞 K) K) (w.under (𝓞 K)))) ∧
    ∀ w : InfinitePlace L, ∃ (v : InfinitePlace K) (θ : ℂ ≃+* ℂ), ∀ a : AdeleRing (𝓞 K) K,
      InfinitePlace.Completion.extensionEmbedding w (((B.β a).1 : InfiniteAdeleRing L) w) =
        θ (InfinitePlace.Completion.extensionEmbedding v ((a.1 : InfiniteAdeleRing K) v)) :=
  ⟨M4aHerbrand.adeleBaseChange_fin_rigidity K L B,
   M4aHerbrand.archRigid_of_corner B fun w => by
      obtain ⟨v, φ, hfin, -, heq⟩ := M4aHerbrand.AdeleBaseChange.exists_arch_corner B w
      exact ⟨v, φ, hfin, heq⟩⟩

#print axioms solution
#print axioms M4aHerbrand.adeleBaseChange_fin_rigidity
#print axioms M4aHerbrand.AdeleBaseChange.exists_arch_corner
#print axioms M4aHerbrand.AdeleBaseChange.beta_snd_apply_eq
#print axioms M4aHerbrand.archRigid_of_corner
#print axioms M4aHerbrand.LocalRigidity.eq_adicCompletionSemialgHom
#print axioms M4aHerbrand.LocalRigidity.under_eq_of_compat
#print axioms M4aHerbrand.ArchRigidityCore.exists_ringEquiv_comp

end S_M4aHerbrand_adeleBaseChange_local_rigidity
end P2MW
export P2MW.S_M4aHerbrand_adeleBaseChange_local_rigidity (solution)
