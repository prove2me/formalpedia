-- Prove2me | solution 1 for M4aHerbrand.subsingleton_ideleGaloisDescent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/4f6628fa-db67-5b12-a6cc-b7b7e9e6c3d4

import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_M4aHerbrand_subsingleton_ideleGaloisDescent

set_option autoImplicit false

namespace M4aHerbrandSolUniq

open M4aHerbrand

section MinIdempotent

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

end MinIdempotent

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

open NumberField IsDedekindDomain

section Assembly

variable (R E F : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
  [Algebra R F] [IsFractionRing R F] [Algebra E F]

def AdeleRigid : Prop :=
  ∀ φ : AdeleRing R F ≃+* AdeleRing R F, Continuous φ → Continuous φ.symm →
    (∀ x : F, φ (algebraMap F (AdeleRing R F) x) = algebraMap F (AdeleRing R F) x) →
    ∀ a, φ a = a

variable {R E F}

theorem descent_continuous_act_symm (D : IdeleGaloisDescent R E F) (g : F ≃ₐ[E] F) :
    Continuous (D.act g).symm := by
  have h := D.continuous_act g⁻¹
  rw [map_inv] at h
  exact h

theorem descent_act_inv_apply_act (D : IdeleGaloisDescent R E F) (g : F ≃ₐ[E] F)
    (a : AdeleRing R F) : D.act g⁻¹ (D.act g a) = a := by
  rw [map_inv, RingAut.inv_apply, RingEquiv.symm_apply_apply]

theorem descent_act_apply_act_inv (D : IdeleGaloisDescent R E F) (g : F ≃ₐ[E] F)
    (a : AdeleRing R F) : D.act g (D.act g⁻¹ a) = a := by
  rw [map_inv, RingAut.inv_apply, RingEquiv.apply_symm_apply]

theorem subsingleton_of_rigid (hrig : AdeleRigid R F) : Subsingleton (IdeleGaloisDescent R E F) := by
  refine ⟨fun D₁ D₂ => ?_⟩
  have hact : ∀ g : F ≃ₐ[E] F, D₁.act g = D₂.act g := by
    intro g

    have key := hrig ((D₁.act g).trans (D₂.act g⁻¹))
      ((D₂.continuous_act g⁻¹).comp (D₁.continuous_act g))
      ((descent_continuous_act_symm D₁ g).comp (descent_continuous_act_symm D₂ g⁻¹))
      (fun x => by
        show D₂.act g⁻¹ (D₁.act g (algebraMap F (AdeleRing R F) x)) = _
        rw [D₁.compat, D₂.compat, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply])
    apply RingEquiv.ext
    intro a
    have ha : D₂.act g⁻¹ (D₁.act g a) = a := key a
    have := congrArg (D₂.act g) ha
    rwa [descent_act_apply_act_inv D₂] at this
  obtain ⟨a₁, c₁, k₁⟩ := D₁
  obtain ⟨a₂, c₂, k₂⟩ := D₂
  have : a₁ = a₂ := MonoidHom.ext hact
  subst this
  rfl

theorem eq_of_forall_mul_indicator_eq [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum R)]
    {a b : AdeleRing R F} (h : ∀ P : PlaceIndex R F, a * indicator R F P = b * indicator R F P) : a = b := by
  refine adele_ext R F (fun v => ?_) (fun w => ?_)
  · have h1 := congrArg (fun x : AdeleRing R F => x.1 v) (h (Sum.inl v))
    rwa [adele_fst_mul, adele_fst_mul, infAdele_mul_apply, infAdele_mul_apply, indicator_inl_fst_same,
      mul_one, mul_one] at h1
  · have h1 := congrArg (fun x : AdeleRing R F => x.2 w) (h (Sum.inr w))
    rwa [adele_snd_mul, adele_snd_mul, finiteAdele_mul_apply, finiteAdele_mul_apply, indicator_inr_snd,
      finiteIndicator_apply_same, mul_one, mul_one] at h1

theorem ringHom_eq_id_of_corners [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum R)]
    (φ : AdeleRing R F →+* AdeleRing R F) (hind : ∀ P, φ (indicator R F P) = indicator R F P)
    (hcorner : ∀ P a, φ (a * indicator R F P) = a * indicator R F P) (a : AdeleRing R F) : φ a = a := by
  refine eq_of_forall_mul_indicator_eq (fun P => ?_)
  rw [← hind P, ← map_mul, hcorner P a, hind P]

end Assembly

open NumberField IsDedekindDomain

section CornerFix

variable (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

theorem denseRange_coe_infinitePlace (v : InfinitePlace F) : DenseRange (fun x : F => (x : v.Completion)) :=
  (NumberField.InfinitePlace.Completion.denseRange_coe v).comp
    (WithAbs.equiv v.1).symm.surjective.denseRange (NumberField.InfinitePlace.Completion.continuous_coe v)

theorem denseRange_coe_finitePlace (w : HeightOneSpectrum R) :
    DenseRange (fun x : F => (x : w.adicCompletion F)) :=
  IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F w

variable [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum R)]

variable {R F}

theorem cornerMap_inl_eq (φ : AdeleRing R F →+* AdeleRing R F) (hφ : Continuous φ)
    (hfix : ∀ x : F, φ (algebraMap F (AdeleRing R F) x) = algebraMap F (AdeleRing R F) x)
    (v : InfinitePlace F) (hind : φ (indicator R F (Sum.inl v)) = indicator R F (Sum.inl v))
    (t : v.Completion) : evalInf R F v (φ (singleInf R F v t)) = t := by
  have hcont : Continuous (fun t : v.Completion => evalInf R F v (φ (singleInf R F v t))) :=
    (continuous_evalInf R F v).comp (hφ.comp (continuous_singleInf R F v))
  have hagree : (fun t : v.Completion => evalInf R F v (φ (singleInf R F v t))) ∘ (fun x : F => (x : v.Completion))
      = id ∘ (fun x : F => (x : v.Completion)) := by
    funext x
    simp only [Function.comp_apply, id_eq]
    have hx : singleInf R F v (x : v.Completion) = algebraMap F (AdeleRing R F) x * indicator R F (Sum.inl v) := by
      rw [mul_indicator_inl, evalInf_algebraMap]
    rw [hx, map_mul, hfix, hind, mul_indicator_inl, evalInf_algebraMap, evalInf_singleInf]
  have := (denseRange_coe_infinitePlace F v).equalizer hcont continuous_id hagree
  exact congrFun this t

theorem cornerMap_inr_eq (φ : AdeleRing R F →+* AdeleRing R F) (hφ : Continuous φ)
    (hfix : ∀ x : F, φ (algebraMap F (AdeleRing R F) x) = algebraMap F (AdeleRing R F) x)
    (w : HeightOneSpectrum R) (hind : φ (indicator R F (Sum.inr w)) = indicator R F (Sum.inr w))
    (t : w.adicCompletion F) : evalFin R F w (φ (singleFin R F w t)) = t := by
  have hcont : Continuous (fun t : w.adicCompletion F => evalFin R F w (φ (singleFin R F w t))) :=
    (continuous_evalFin R F w).comp (hφ.comp (continuous_singleFin R F w))
  have hagree : (fun t : w.adicCompletion F => evalFin R F w (φ (singleFin R F w t))) ∘
      (fun x : F => (x : w.adicCompletion F)) = id ∘ (fun x : F => (x : w.adicCompletion F)) := by
    funext x
    simp only [Function.comp_apply, id_eq]
    have hx : singleFin R F w (x : w.adicCompletion F)
        = algebraMap F (AdeleRing R F) x * indicator R F (Sum.inr w) := by
      rw [mul_indicator_inr, evalFin_algebraMap]
    rw [hx, map_mul, hfix, hind, mul_indicator_inr, evalFin_algebraMap, evalFin_singleFin]
  have := (denseRange_coe_finitePlace R F w).equalizer hcont continuous_id hagree
  exact congrFun this t

theorem map_singleInf (φ : AdeleRing R F →+* AdeleRing R F) (hφ : Continuous φ)
    (hfix : ∀ x : F, φ (algebraMap F (AdeleRing R F) x) = algebraMap F (AdeleRing R F) x)
    (v : InfinitePlace F) (hind : φ (indicator R F (Sum.inl v)) = indicator R F (Sum.inl v))
    (t : v.Completion) : φ (singleInf R F v t) = singleInf R F v t := by
  have h1 : φ (singleInf R F v t) = φ (singleInf R F v t) * indicator R F (Sum.inl v) := by
    conv_lhs => rw [← singleInf_mul_indicator R F v t, map_mul, hind]
  rw [h1, mul_indicator_inl, cornerMap_inl_eq φ hφ hfix v hind]

theorem map_singleFin (φ : AdeleRing R F →+* AdeleRing R F) (hφ : Continuous φ)
    (hfix : ∀ x : F, φ (algebraMap F (AdeleRing R F) x) = algebraMap F (AdeleRing R F) x)
    (w : HeightOneSpectrum R) (hind : φ (indicator R F (Sum.inr w)) = indicator R F (Sum.inr w))
    (t : w.adicCompletion F) : φ (singleFin R F w t) = singleFin R F w t := by
  have h1 : φ (singleFin R F w t) = φ (singleFin R F w t) * indicator R F (Sum.inr w) := by
    conv_lhs => rw [← singleFin_mul_indicator R F w t, map_mul, hind]
  rw [h1, mul_indicator_inr, cornerMap_inr_eq φ hφ hfix w hind]

theorem eq_id_of_fix_diagonal_of_fix_indicator (φ : AdeleRing R F →+* AdeleRing R F) (hφ : Continuous φ)
    (hfix : ∀ x : F, φ (algebraMap F (AdeleRing R F) x) = algebraMap F (AdeleRing R F) x)
    (hind : ∀ P, φ (indicator R F P) = indicator R F P) (a : AdeleRing R F) : φ a = a := by
  refine ringHom_eq_id_of_corners φ hind (fun P b => ?_) a
  rcases P with v | w
  · rw [mul_indicator_inl, map_singleInf φ hφ hfix v (hind _)]
  · rw [mul_indicator_inr, map_singleFin φ hφ hfix w (hind _)]

variable (R F)

theorem adeleRigid_of_indicator_fixed
    (hsep : ∀ φ : AdeleRing R F ≃+* AdeleRing R F, Continuous φ → Continuous φ.symm →
      (∀ x : F, φ (algebraMap F (AdeleRing R F) x) = algebraMap F (AdeleRing R F) x) →
      ∀ P, φ (indicator R F P) = indicator R F P) :
    AdeleRigid R F := by
  intro φ hφ hφ' hfix a
  exact eq_id_of_fix_diagonal_of_fix_indicator φ.toRingHom hφ hfix (hsep φ hφ hφ' hfix) a

end CornerFix

open NumberField IsDedekindDomain Filter Topology

section ValuedCriterion

theorem v_lt_one_of_tendsto_pow {K Γ₀ : Type*} [Ring K] [LinearOrderedCommGroupWithZero Γ₀]
    [hv : Valued K Γ₀] {x : K} (h : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0)) : Valued.v x < 1 := by
  by_contra hx
  rw [not_lt] at hx
  have hmem : {y : K | hv.v.restrict y
      < ((1 : (MonoidWithZeroHom.ValueGroup₀ (.ofClass hv.v))ˣ) :
        MonoidWithZeroHom.ValueGroup₀ (.ofClass hv.v))} ∈ 𝓝 (0 : K) :=
    Valued.mem_nhds_zero.mpr ⟨1, fun _ hy => hy⟩
  have hev := h.eventually_mem hmem
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have hN' := hN N le_rfl
  rw [Set.mem_setOf_eq, Units.val_one] at hN'

  have h2 : hv.v (x ^ N) < 1 := (Valuation.restrict_lt_one_iff _).mp hN'
  rw [map_pow] at h2
  exact absurd h2 (not_lt.mpr (one_le_pow_of_one_le' hx N))

end ValuedCriterion

section Separation

variable (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

variable [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum R)]

def IsNilAt (P : PlaceIndex R F) (x : F) : Prop :=
  Tendsto (fun n : ℕ => (algebraMap F (AdeleRing R F) x * indicator R F P) ^ (n + 1)) atTop (𝓝 0)

theorem corner_pow_succ (P : PlaceIndex R F) (x : F) (n : ℕ) :
    (algebraMap F (AdeleRing R F) x * indicator R F P) ^ (n + 1)
      = algebraMap F (AdeleRing R F) (x ^ (n + 1)) * indicator R F P := by
  rw [mul_pow, (isIdempotentElem_indicator R F P).pow_succ_eq, map_pow]

theorem singleInf_zero (v : InfinitePlace F) : singleInf R F v 0 = 0 := by
  have h := mul_indicator_inl R F 0 v
  rw [map_zero, zero_mul] at h
  exact h.symm

theorem singleFin_zero (w : HeightOneSpectrum R) : singleFin R F w 0 = 0 := by
  have h := mul_indicator_inr R F 0 w
  rw [map_zero, zero_mul] at h
  exact h.symm

omit [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum R)] in
theorem norm_coe_infinitePlace (v : InfinitePlace F) (x : F) : ‖(x : v.Completion)‖ = v x := by
  rw [NumberField.InfinitePlace.Completion.norm_coe]
  rfl

variable {R F}

theorem IsNilAt.map (φ : AdeleRing R F →+* AdeleRing R F) (hφ : Continuous φ)
    (hfix : ∀ x : F, φ (algebraMap F (AdeleRing R F) x) = algebraMap F (AdeleRing R F) x)
    {P Q : PlaceIndex R F} (hPQ : φ (indicator R F P) = indicator R F Q) {x : F}
    (hx : IsNilAt R F P x) : IsNilAt R F Q x := by
  unfold IsNilAt at hx ⊢
  have h0 : Tendsto φ (𝓝 0) (𝓝 0) := by
    have := hφ.tendsto 0
    rwa [map_zero] at this
  refine (h0.comp hx).congr (fun n => ?_)
  show φ ((algebraMap F (AdeleRing R F) x * indicator R F P) ^ (n + 1)) = _
  rw [map_pow, map_mul, hfix, hPQ]

variable (R F)

theorem isNilAt_inl_iff (v : InfinitePlace F) (x : F) : IsNilAt R F (Sum.inl v) x ↔ v x < 1 := by
  unfold IsNilAt
  have hseq : (fun n : ℕ => (algebraMap F (AdeleRing R F) x * indicator R F (Sum.inl v)) ^ (n + 1))
      = fun n => singleInf R F v ((x : v.Completion) ^ (n + 1)) := by
    funext n
    rw [corner_pow_succ, mul_indicator_inl, map_pow, map_pow, evalInf_algebraMap]
  rw [hseq, ← norm_coe_infinitePlace F v x, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one,
    ← Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => (x : v.Completion) ^ n) 1]
  constructor
  · intro h
    have h2 := ((continuous_evalInf R F v).tendsto 0).comp h
    rw [map_zero] at h2
    refine h2.congr (fun n => ?_)
    show evalInf R F v (singleInf R F v _) = _
    rw [evalInf_singleInf]
  · intro h
    have h2 := ((continuous_singleInf R F v).tendsto 0).comp h
    rw [singleInf_zero] at h2
    exact h2

theorem isNilAt_inr_iff (w : HeightOneSpectrum R) (x : F) :
    IsNilAt R F (Sum.inr w) x ↔ w.valuation F x < 1 := by
  unfold IsNilAt
  have hseq : (fun n : ℕ => (algebraMap F (AdeleRing R F) x * indicator R F (Sum.inr w)) ^ (n + 1))
      = fun n => singleFin R F w ((x : w.adicCompletion F) ^ (n + 1)) := by
    funext n
    rw [corner_pow_succ, mul_indicator_inr, map_pow, map_pow, evalFin_algebraMap]
  rw [hseq, ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x]
  constructor
  · intro h
    have h2 := ((continuous_evalFin R F w).tendsto 0).comp h
    rw [map_zero] at h2
    have h1 : Tendsto (fun n : ℕ => (x : w.adicCompletion F) ^ (n + 1)) atTop (𝓝 0) := by
      refine h2.congr (fun n => ?_)
      show evalFin R F w (singleFin R F w _) = _
      rw [evalFin_singleFin]
    exact v_lt_one_of_tendsto_pow
      ((Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => (x : w.adicCompletion F) ^ n) 1).mp h1)
  · intro hx
    have h1 : Tendsto (fun n : ℕ => (x : w.adicCompletion F) ^ (n + 1)) atTop (𝓝 0) :=
      (Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => (x : w.adicCompletion F) ^ n) 1).mpr
        (Valued.tendsto_zero_pow_of_v_lt_one hx)
    have h2 := ((continuous_singleFin R F w).tendsto 0).comp h1
    rw [singleFin_zero] at h2
    exact h2

omit [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum R)] in

theorem infinitePlace_eq_of_forall_lt_one_iff {v v' : InfinitePlace F}
    (h : ∀ x : F, v x < 1 ↔ v' x < 1) : v = v' :=
  NumberField.InfinitePlace.eq_iff_isEquiv.mpr (AbsoluteValue.isEquiv_iff_lt_one_iff.mpr h)

omit [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum R)] in

theorem heightOneSpectrum_eq_of_forall_lt_one_iff {w w' : HeightOneSpectrum R}
    (h : ∀ x : F, w.valuation F x < 1 ↔ w'.valuation F x < 1) : w = w' := by
  refine HeightOneSpectrum.ext (le_antisymm (fun r hr => ?_) (fun r hr => ?_))
  · exact (HeightOneSpectrum.valuation_lt_one_iff_mem w' r).mp
      ((h _).mp ((HeightOneSpectrum.valuation_lt_one_iff_mem w r).mpr hr))
  · exact (HeightOneSpectrum.valuation_lt_one_iff_mem w r).mp
      ((h _).mpr ((HeightOneSpectrum.valuation_lt_one_iff_mem w' r).mpr hr))

omit [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum R)] in

theorem infinitePlace_two_inv_lt_one (v : InfinitePlace F) : v (2⁻¹ : F) < 1 := by
  have h2 : v (2 : F) = 2 := by
    have := NumberField.InfinitePlace.map_natCast v 2
    simpa using this
  rw [map_inv₀, h2]
  norm_num

omit [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum R)] in

theorem two_ne_zero_of_infinitePlace (v : InfinitePlace F) : (2 : F) ≠ 0 := by
  intro h
  have h2 : v (2 : F) = 2 := by
    have := NumberField.InfinitePlace.map_natCast v 2
    simpa using this
  rw [h, map_zero] at h2
  norm_num at h2

omit [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum R)] in

theorem not_valuation_two_inv_lt_one (w : HeightOneSpectrum R) (h2 : (2 : F) ≠ 0) :
    ¬ w.valuation F (2⁻¹ : F) < 1 := by
  rw [Valuation.val_lt_one_iff _ (inv_ne_zero h2), inv_inv, not_lt]
  have : w.valuation F (algebraMap R F 2) ≤ 1 := HeightOneSpectrum.valuation_le_one w 2
  rwa [map_ofNat] at this

theorem placeIndex_eq_of_isNilAt_iff {P Q : PlaceIndex R F} (h : ∀ x : F, IsNilAt R F P x ↔ IsNilAt R F Q x) :
    P = Q := by
  rcases P with v | w <;> rcases Q with v' | w'
  · have h' : ∀ x : F, v x < 1 ↔ v' x < 1 := fun x => by
      rw [← isNilAt_inl_iff R F v x, ← isNilAt_inl_iff R F v' x]; exact h x
    exact congrArg Sum.inl (infinitePlace_eq_of_forall_lt_one_iff (F := F) h')
  · exfalso
    have h' := (h (2⁻¹ : F)).mp ((isNilAt_inl_iff R F v _).mpr (infinitePlace_two_inv_lt_one (F := F) v))
    rw [isNilAt_inr_iff] at h'
    exact not_valuation_two_inv_lt_one (R := R) (F := F) w' (two_ne_zero_of_infinitePlace (F := F) v) h'
  · exfalso
    have h' := (h (2⁻¹ : F)).mpr ((isNilAt_inl_iff R F v' _).mpr (infinitePlace_two_inv_lt_one (F := F) v'))
    rw [isNilAt_inr_iff] at h'
    exact not_valuation_two_inv_lt_one (R := R) (F := F) w (two_ne_zero_of_infinitePlace (F := F) v') h'
  · have h' : ∀ x : F, w.valuation F x < 1 ↔ w'.valuation F x < 1 := fun x => by
      rw [← isNilAt_inr_iff R F w x, ← isNilAt_inr_iff R F w' x]; exact h x
    exact congrArg Sum.inr (heightOneSpectrum_eq_of_forall_lt_one_iff (R := R) (F := F) h')

theorem indicator_fixed (φ : AdeleRing R F ≃+* AdeleRing R F) (hφ : Continuous φ) (hφ' : Continuous φ.symm)
    (hfix : ∀ x : F, φ (algebraMap F (AdeleRing R F) x) = algebraMap F (AdeleRing R F) x)
    (P : PlaceIndex R F) : φ (indicator R F P) = indicator R F P := by
  obtain ⟨Q, hQ⟩ := AdeleRing.exists_ringEquiv_indicator_eq R F φ P
  have hQ' : φ.symm (indicator R F Q) = indicator R F P := by
    rw [← hQ, RingEquiv.symm_apply_apply]
  have hfix' : ∀ x : F, φ.symm (algebraMap F (AdeleRing R F) x) = algebraMap F (AdeleRing R F) x := by
    intro x
    conv_lhs => rw [← hfix x]
    rw [RingEquiv.symm_apply_apply]
  have hPQ : P = Q := by
    refine placeIndex_eq_of_isNilAt_iff R F (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
    · exact hx.map φ.toRingHom hφ hfix hQ
    · exact hx.map φ.symm.toRingHom hφ' hfix' hQ'
  subst hPQ
  exact hQ

theorem adeleRigid : AdeleRigid R F :=
  adeleRigid_of_indicator_fixed R F (indicator_fixed R F)

end Separation

section Uniqueness

variable (R E F : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
  [Algebra R F] [IsFractionRing R F] [Algebra E F]

theorem subsingleton_ideleGaloisDescent_impl : Subsingleton (IdeleGaloisDescent R E F) := by
  classical
  exact subsingleton_of_rigid (adeleRigid R F)

end Uniqueness

end M4aHerbrandSolUniq

theorem solution (R E F : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
    [Algebra R F] [IsFractionRing R F] [Algebra E F] :
    Subsingleton (M4aHerbrand.IdeleGaloisDescent R E F) :=
  M4aHerbrandSolUniq.subsingleton_ideleGaloisDescent_impl R E F

#print axioms solution

end S_M4aHerbrand_subsingleton_ideleGaloisDescent
end P2MW
export P2MW.S_M4aHerbrand_subsingleton_ideleGaloisDescent (solution)
