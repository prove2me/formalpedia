-- Prove2me | solution 1 for NumberField.Idele.exists_finset_forall_semiLocalCharacter_eq_one_and_eq_mul_prod_semiLocalCharacter_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/b6c61ede-9ca7-5496-b69a-9640fbce0af9

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_exists_finset_forall_semiLocalCharacter_eq_one_and_eq_mul_prod_semiLocalCharacter_of_continuous

set_option autoImplicit false

open IsDedekindDomain NumberField Topology Filter
open NumberField.AdelicLevel TensorProduct AutomorphicForm
open scoped TensorProduct

noncomputable section

namespace TwistedUnipotentTermK7

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev SL (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Type :=
  L ⊗[K] v.adicCompletion K

scoped instance instFiniteExtension (v : HeightOneSpectrum (𝓞 K)) : Finite (v.Extension (𝓞 L)) :=
  HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v

noncomputable scoped instance instFintypeExtension (v : HeightOneSpectrum (𝓞 K)) : Fintype (v.Extension (𝓞 L)) :=
  Fintype.ofFinite _

variable (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)

def ξfun (t : (AdeleRing (𝓞 L) L)ˣ) : ℂ := ((ξL ⟨t, Subgroup.mem_top t⟩ : ℂˣ) : ℂ)

def ξhom : (AdeleRing (𝓞 L) L)ˣ →* ℂ where
  toFun := ξfun ξL
  map_one' := by
    simp only [ξfun]
    have : (⟨(1 : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ)) = 1 := rfl
    rw [this, map_one, Units.val_one]
  map_mul' s t := by
    simp only [ξfun]
    have : (⟨s * t, Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ)) =
        ⟨s, Subgroup.mem_top s⟩ * ⟨t, Subgroup.mem_top t⟩ := rfl
    rw [this, map_mul, Units.val_mul]

theorem ξhom_apply (t : (AdeleRing (𝓞 L) L)ˣ) : ξhom ξL t = ((ξL ⟨t, Subgroup.mem_top t⟩ : ℂˣ) : ℂ) := rfl

variable (K L)
variable (v : HeightOneSpectrum (𝓞 K))

theorem semiLocalUnitComponent_one (w : v.Extension (𝓞 L)) :
    TwistedUnipotentTerm.semiLocalUnitComponent K L v w 1 = 1 := by
  simp [TwistedUnipotentTerm.semiLocalUnitComponent]

theorem semiLocalUnitComponent_mul (w : v.Extension (𝓞 L)) (a b : (SL K L v)ˣ) :
    TwistedUnipotentTerm.semiLocalUnitComponent K L v w (a * b) =
      TwistedUnipotentTerm.semiLocalUnitComponent K L v w a * TwistedUnipotentTerm.semiLocalUnitComponent K L v w b := by
  simp [TwistedUnipotentTerm.semiLocalUnitComponent]

theorem semiLocalUnitComponent_inv (w : v.Extension (𝓞 L)) (a : (SL K L v)ˣ) :
    TwistedUnipotentTerm.semiLocalUnitComponent K L v w a⁻¹ =
      (TwistedUnipotentTerm.semiLocalUnitComponent K L v w a)⁻¹ := by
  simp [TwistedUnipotentTerm.semiLocalUnitComponent]

theorem coe_semiLocalUnitComponent (w : v.Extension (𝓞 L)) (a : (SL K L v)ˣ) :
    ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w a : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) =
      HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v (a : SL K L v) w := rfl

def idele : (SL K L v)ˣ →* (AdeleRing (𝓞 L) L)ˣ where
  toFun ζ := ∏ w : v.Extension (𝓞 L),
    Matrix.GeneralLinearGroup.det
      (heckeGenAt (𝓞 L) L w.1 (TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ))
  map_one' := Finset.prod_eq_one fun w _ => by rw [semiLocalUnitComponent_one, map_one, map_one]
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w _ => by rw [semiLocalUnitComponent_mul, map_mul, map_mul]

theorem idele_apply (ζ : (SL K L v)ˣ) : idele K L v ζ = ∏ w : v.Extension (𝓞 L),
    Matrix.GeneralLinearGroup.det
      (heckeGenAt (𝓞 L) L w.1 (TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ)) := rfl

theorem semiLocalCharacter_eq (ζ : (SL K L v)ˣ) :
    TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ = ξhom ξL (idele K L v ζ) := by
  unfold TwistedUnipotentTerm.semiLocalCharacter
  rw [idele_apply, finprod_eq_prod_of_fintype, map_prod]
  rfl

omit [NumberField K] in
theorem det_diagOne {A : Type*} [CommRing A] (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det (Matrix.diagonal ![(a : A), 1]) = a
  rw [Matrix.det_diagonal]
  simp

theorem val_det_heckeGenAt (w : HeightOneSpectrum (𝓞 L)) (t : (w.adicCompletion L)ˣ) :
    ((Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 L) L w t) : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) =
      finIncl (𝓞 L) L (localUnit (𝓞 L) L w t : (FiniteAdeleRing (𝓞 L) L)ˣ) := by
  unfold heckeGenAt
  rw [MonoidHom.comp_apply, det_diagOne]
  rfl

theorem val_det_heckeGenAt_fst (w : HeightOneSpectrum (𝓞 L)) (t : (w.adicCompletion L)ˣ) :
    ((Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 L) L w t) : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 = 1 := by
  rw [val_det_heckeGenAt]; rfl

theorem val_det_heckeGenAt_snd (w : HeightOneSpectrum (𝓞 L)) (t : (w.adicCompletion L)ˣ) :
    ((Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 L) L w t) : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 =
      (localUnit (𝓞 L) L w t : (FiniteAdeleRing (𝓞 L) L)ˣ) := by
  rw [val_det_heckeGenAt]; rfl

omit [NumberField K] in
theorem fst_prod {ι : Type*} (s : Finset ι) (f : ι → AdeleRing (𝓞 L) L) :
    (∏ i ∈ s, f i).1 = ∏ i ∈ s, (f i).1 :=
  map_prod (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) f s

omit [NumberField K] in
theorem snd_prod {ι : Type*} (s : Finset ι) (f : ι → AdeleRing (𝓞 L) L) :
    (∏ i ∈ s, f i).2 = ∏ i ∈ s, (f i).2 :=
  map_prod (RingHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) f s

omit [NumberField K] in
theorem finAdele_prod_apply {ι : Type*} (s : Finset ι) (f : ι → FiniteAdeleRing (𝓞 L) L)
    (w : HeightOneSpectrum (𝓞 L)) : (∏ i ∈ s, f i) w = ∏ i ∈ s, f i w :=
  map_prod (finAdeleEval (𝓞 L) L w) f s

omit [NumberField K] in
theorem fst_val_mul (a b : (AdeleRing (𝓞 L) L)ˣ) :
    ((a * b : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 = (a : AdeleRing (𝓞 L) L).1 * (b : AdeleRing (𝓞 L) L).1 :=
  rfl

omit [NumberField K] in
theorem snd_val_mul_apply (a b : (AdeleRing (𝓞 L) L)ˣ) (w : HeightOneSpectrum (𝓞 L)) :
    ((a * b : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w =
      (a : AdeleRing (𝓞 L) L).2 w * (b : AdeleRing (𝓞 L) L).2 w :=
  rfl

omit [NumberField K] in
theorem fst_val_mul_inv (t : (AdeleRing (𝓞 L) L)ˣ) :
    (t : AdeleRing (𝓞 L) L).1 * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 = 1 := by
  rw [← fst_val_mul, mul_inv_cancel]; rfl

omit [NumberField K] in
theorem snd_val_mul_inv_apply (t : (AdeleRing (𝓞 L) L)ˣ) (w : HeightOneSpectrum (𝓞 L)) :
    (t : AdeleRing (𝓞 L) L).2 w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w = 1 := by
  rw [← snd_val_mul_apply, mul_inv_cancel]; rfl

omit [NumberField K] in
theorem snd_val_inv_mul_apply (t : (AdeleRing (𝓞 L) L)ˣ) (w : HeightOneSpectrum (𝓞 L)) :
    ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w * (t : AdeleRing (𝓞 L) L).2 w = 1 := by
  rw [← snd_val_mul_apply, inv_mul_cancel]; rfl

theorem val_idele_fst (ζ : (SL K L v)ˣ) : ((idele K L v ζ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 = 1 := by
  rw [idele_apply, Units.coe_prod, fst_prod]
  exact Finset.prod_eq_one fun w _ => val_det_heckeGenAt_fst L _ _

theorem val_idele_snd (ζ : (SL K L v)ˣ) :
    ((idele K L v ζ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 =
      ∏ w : v.Extension (𝓞 L),
        ((localUnit (𝓞 L) L w.1 (TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ) :
          (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) := by
  rw [idele_apply, Units.coe_prod, snd_prod]
  exact Finset.prod_congr rfl fun w _ => val_det_heckeGenAt_snd L _ _

open scoped Classical in

theorem val_idele_snd_apply (ζ : (SL K L v)ˣ) (w' : HeightOneSpectrum (𝓞 L)) :
    ((idele K L v ζ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w' =
      if h : w'.under (𝓞 K) = v then
        ((TwistedUnipotentTerm.semiLocalUnitComponent K L v ⟨w', h⟩ ζ : (w'.adicCompletion L)ˣ) :
          w'.adicCompletion L)
      else 1 := by
  rw [val_idele_snd, finAdele_prod_apply]
  by_cases h : w'.under (𝓞 K) = v
  · rw [dif_pos h]
    refine (Finset.prod_eq_single (⟨w', h⟩ : v.Extension (𝓞 L)) ?_ ?_).trans ?_
    · intro w _ hw
      exact localUnit_apply_of_ne (𝓞 L) L w.1 _ fun h' => hw (Subtype.ext h'.symm)
    · intro h'; exact absurd (Finset.mem_univ (α := v.Extension (𝓞 L)) _) h'
    · exact localUnit_apply_self (𝓞 L) L w' _
  · rw [dif_neg h]
    refine Finset.prod_eq_one fun w _ => localUnit_apply_of_ne (𝓞 L) L w.1 _ fun h' => h ?_
    rw [h', w.2]

theorem val_prod_idele_fst {ι : Type*} (s : Finset ι) (vs : ι → HeightOneSpectrum (𝓞 K))
    (f : ∀ i, (SL K L (vs i))ˣ) :
    ((∏ i ∈ s, idele K L (vs i) (f i) : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 = 1 := by
  rw [Units.coe_prod, fst_prod]
  exact Finset.prod_eq_one fun i _ => val_idele_fst K L (vs i) (f i)

open scoped Classical in

theorem val_prod_idele_snd_apply (S : Finset (HeightOneSpectrum (𝓞 K))) (f : ∀ v, (SL K L v)ˣ)
    (w : HeightOneSpectrum (𝓞 L)) :
    ((∏ v ∈ S, idele K L v (f v) : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w =
      if w.under (𝓞 K) ∈ S then
        ((TwistedUnipotentTerm.semiLocalUnitComponent K L (w.under (𝓞 K)) ⟨w, rfl⟩ (f (w.under (𝓞 K))) :
          (w.adicCompletion L)ˣ) : w.adicCompletion L)
      else 1 := by
  rw [Units.coe_prod, snd_prod, finAdele_prod_apply]
  simp_rw [val_idele_snd_apply]
  by_cases h : w.under (𝓞 K) ∈ S
  · rw [if_pos h, Finset.prod_eq_single (w.under (𝓞 K))]
    · rw [dif_pos rfl]
    · intro v _ hv
      rw [dif_neg (Ne.symm hv)]
    · intro h'; exact absurd h h'
  · rw [if_neg h]
    refine Finset.prod_eq_one fun v hv => ?_
    rw [dif_neg]
    rintro rfl
    exact h hv

theorem semiLocalEval_apply (v' : HeightOneSpectrum (𝓞 K)) (x : FiniteAdeleRing (𝓞 L) L) :
    semiLocalEval K L v' x =
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v').symm (fun w => x w.1) := by
  simp only [AutomorphicForm.semiLocalEval, RingHom.coe_comp, Function.comp_apply]
  rfl

theorem baseChangeAlgEquiv_semiLocalEval (v' : HeightOneSpectrum (𝓞 K)) (x : FiniteAdeleRing (𝓞 L) L) :
    HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v' (semiLocalEval K L v' x) =
      fun w : v'.Extension (𝓞 L) => x w.1 := by
  rw [semiLocalEval_apply, AlgEquiv.apply_symm_apply]

theorem coe_semiLocalUnitComponent_semiLocalIdele (w : v.Extension (𝓞 L)) (t : (AdeleRing (𝓞 L) L)ˣ) :
    ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w (TransversalMeasure.semiLocalIdele K L v t) :
      (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) = (t : AdeleRing (𝓞 L) L).2 w.1 := by
  rw [coe_semiLocalUnitComponent]
  have : ((TransversalMeasure.semiLocalIdele K L v t : (SL K L v)ˣ) : SL K L v) =
      semiLocalEval K L v (t : AdeleRing (𝓞 L) L).2 := rfl
  rw [this, baseChangeAlgEquiv_semiLocalEval]

theorem mem_semiLocalIntegers_iff (x : SL K L v) :
    x ∈ semiLocalIntegers K L v ↔
      ∀ w : v.Extension (𝓞 L),
        HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w ∈ w.1.adicCompletionIntegers L := by
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, piIntegers, Set.mem_univ_pi]
  rfl

theorem coe_mem_semiLocalIntegers_of_mem_integralUnits {u : (SL K L v)ˣ}
    (hu : u ∈ TransversalMeasure.integralUnits K L v) :
    (u : SL K L v) ∈ semiLocalIntegers K L v ∧ ((u⁻¹ : (SL K L v)ˣ) : SL K L v) ∈ semiLocalIntegers K L v := by
  have h := (Submonoid.mem_units_iff _ _).1 hu
  exact ⟨h.1, h.2⟩

theorem coe_semiLocalUnitComponent_mem_of_mem_integralUnits {u : (SL K L v)ˣ}
    (hu : u ∈ TransversalMeasure.integralUnits K L v) (w : v.Extension (𝓞 L)) :
    ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w u : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) ∈
        w.1.adicCompletionIntegers L ∧
      (((TwistedUnipotentTerm.semiLocalUnitComponent K L v w u)⁻¹ : (w.1.adicCompletion L)ˣ) :
        w.1.adicCompletion L) ∈ w.1.adicCompletionIntegers L := by
  obtain ⟨h1, h2⟩ := coe_mem_semiLocalIntegers_of_mem_integralUnits K L v hu
  refine ⟨?_, ?_⟩
  · rw [coe_semiLocalUnitComponent]
    exact (mem_semiLocalIntegers_iff K L v _).1 h1 w
  · rw [← semiLocalUnitComponent_inv, coe_semiLocalUnitComponent]
    exact (mem_semiLocalIntegers_iff K L v _).1 h2 w

omit [NumberField K] in

theorem eq_one_of_forall_norm_pow_two_pow_sub_one_lt {z : ℂ} (h : ∀ n : ℕ, ‖z ^ (2 ^ n) - 1‖ < 1 / 2) : z = 1 := by
  by_contra hz
  have hd : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  have key : ∀ n : ℕ, (3 / 2 : ℝ) ^ n * ‖z - 1‖ ≤ ‖z ^ (2 ^ n) - 1‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hlt := h n
      have hfac : z ^ (2 ^ (n + 1)) - 1 = (z ^ (2 ^ n) - 1) * (z ^ (2 ^ n) + 1) := by ring
      have hge : (3 / 2 : ℝ) ≤ ‖z ^ (2 ^ n) + 1‖ := by
        have h2 := norm_sub_norm_le (2 : ℂ) (1 - z ^ (2 ^ n))
        have h3 : (2 : ℂ) - (1 - z ^ (2 ^ n)) = z ^ (2 ^ n) + 1 := by ring
        rw [h3, norm_sub_rev, Complex.norm_two] at h2
        linarith
      calc (3 / 2 : ℝ) ^ (n + 1) * ‖z - 1‖ = (3 / 2) ^ n * ‖z - 1‖ * (3 / 2) := by ring
        _ ≤ ‖z ^ (2 ^ n) - 1‖ * ‖z ^ (2 ^ n) + 1‖ :=
            mul_le_mul ih hge (by norm_num) (norm_nonneg _)
        _ = ‖z ^ (2 ^ (n + 1)) - 1‖ := by rw [hfac, norm_mul]
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := key n
  have h2 := h n
  rw [div_lt_iff₀ hd] at hn
  linarith

section UnitIdeles

abbrev UnitPi (L : Type) [Field L] [NumberField L] : Type :=
  ∀ w : HeightOneSpectrum (𝓞 L), (w.adicCompletionIntegers L)ˣ

def finOf (x : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletionIntegers L) : FiniteAdeleRing (𝓞 L) L :=
  ⟨fun w => (x w : w.adicCompletion L), Filter.Eventually.of_forall fun w => (x w).2⟩

omit [NumberField K] in
theorem finOf_apply (x : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletionIntegers L) (w : HeightOneSpectrum (𝓞 L)) :
    finOf L x w = (x w : w.adicCompletion L) := rfl

omit [NumberField K] in
theorem finOf_one : finOf L 1 = 1 := FiniteAdeleRing.ext L fun _ => rfl

omit [NumberField K] in
theorem finOf_mul (x y : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletionIntegers L) :
    finOf L (x * y) = finOf L x * finOf L y := FiniteAdeleRing.ext L fun _ => rfl

omit [NumberField K] in

theorem continuous_finOf : Continuous (finOf L) := by
  have h1 := (RestrictedProduct.isEmbedding_structureMap
    (R := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
    (A := fun w => ((w.adicCompletionIntegers L : Set (w.adicCompletion L))))
    (𝓕 := Filter.cofinite)).continuous
  have h2 : Continuous fun x : (∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletionIntegers L) =>
      fun w => (⟨(x w : w.adicCompletion L), (x w).2⟩ :
        ((w.adicCompletionIntegers L : Set (w.adicCompletion L)))) :=
    continuous_pi fun w => (continuous_subtype_val.comp (continuous_apply w)).subtype_mk _
  exact h1.comp h2

def unitIdele : UnitPi L →* (AdeleRing (𝓞 L) L)ˣ where
  toFun u :=
    ⟨((1 : InfiniteAdeleRing L), finOf L fun w => (u w : w.adicCompletionIntegers L)),
      ((1 : InfiniteAdeleRing L), finOf L fun w => (((u w)⁻¹ : (w.adicCompletionIntegers L)ˣ) :
        w.adicCompletionIntegers L)),
      Prod.ext (one_mul _) (by
        show (finOf L fun w => (u w : w.adicCompletionIntegers L)) *
            (finOf L fun w => (((u w)⁻¹ : (w.adicCompletionIntegers L)ˣ) : w.adicCompletionIntegers L)) = 1
        rw [← finOf_mul, ← finOf_one]
        congr 1
        funext w
        exact Units.mul_inv (u w)),
      Prod.ext (one_mul _) (by
        show (finOf L fun w => (((u w)⁻¹ : (w.adicCompletionIntegers L)ˣ) : w.adicCompletionIntegers L)) *
            (finOf L fun w => (u w : w.adicCompletionIntegers L)) = 1
        rw [← finOf_mul, ← finOf_one]
        congr 1
        funext w
        exact Units.inv_mul (u w))⟩
  map_one' := Units.ext (Prod.ext rfl (FiniteAdeleRing.ext L fun _ => rfl))
  map_mul' _ _ := Units.ext (Prod.ext (one_mul _).symm (FiniteAdeleRing.ext L fun _ => rfl))

omit [NumberField K] in
theorem val_unitIdele_fst (u : UnitPi L) : ((unitIdele L u : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 = 1 :=
  rfl

omit [NumberField K] in
theorem val_unitIdele_snd_apply (u : UnitPi L) (w : HeightOneSpectrum (𝓞 L)) :
    ((unitIdele L u : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w = ((u w : w.adicCompletionIntegers L) :
      w.adicCompletion L) :=
  rfl

omit [NumberField K] in

theorem continuous_unitIdele : Continuous (unitIdele L) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun u : UnitPi L =>
      (((1 : InfiniteAdeleRing L), finOf L fun w => (u w : w.adicCompletionIntegers L)) : AdeleRing (𝓞 L) L)
    exact continuous_const.prodMk ((continuous_finOf L).comp
      (continuous_pi fun w => Units.continuous_val.comp (continuous_apply w)))
  · show Continuous fun u : UnitPi L =>
      (((1 : InfiniteAdeleRing L), finOf L fun w => (((u w)⁻¹ : (w.adicCompletionIntegers L)ˣ) :
        w.adicCompletionIntegers L)) : AdeleRing (𝓞 L) L)
    exact continuous_const.prodMk ((continuous_finOf L).comp
      (continuous_pi fun w => Units.continuous_coe_inv.comp (continuous_apply w)))

variable {L}

omit [NumberField K] in

theorem exists_finset_forall_norm_sub_one_lt
    (hc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ξhom ξL z) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 L)), ∀ u : UnitPi L, (∀ w ∈ T, u w = 1) →
      ‖ξhom ξL (unitIdele L u) - 1‖ < 1 / 2 := by
  have hopen : IsOpen {u : UnitPi L | ‖ξhom ξL (unitIdele L u) - 1‖ < 1 / 2} :=
    isOpen_lt ((hc.comp (continuous_unitIdele L)).sub continuous_const).norm continuous_const
  have hmem : (1 : UnitPi L) ∈ {u : UnitPi L | ‖ξhom ξL (unitIdele L u) - 1‖ < 1 / 2} := by
    show ‖ξhom ξL (unitIdele L 1) - 1‖ < 1 / 2
    rw [map_one, map_one, sub_self, norm_zero]
    norm_num
  obtain ⟨I, t, ht, hsub⟩ := isOpen_pi_iff.1 hopen 1 hmem
  refine ⟨I, fun u hu => hsub (Set.mem_pi.2 fun w hw => ?_)⟩
  rw [hu w (Finset.mem_coe.1 hw)]
  exact (ht w (Finset.mem_coe.1 hw)).2

omit [NumberField K] in

theorem apply_unitIdele_eq_one {T : Finset (HeightOneSpectrum (𝓞 L))}
    (hT : ∀ u : UnitPi L, (∀ w ∈ T, u w = 1) → ‖ξhom ξL (unitIdele L u) - 1‖ < 1 / 2)
    (u : UnitPi L) (hu : ∀ w ∈ T, u w = 1) : ξhom ξL (unitIdele L u) = 1 := by
  refine eq_one_of_forall_norm_pow_two_pow_sub_one_lt fun n => ?_
  rw [← map_pow, ← map_pow]
  exact hT _ fun w hw => by rw [Pi.pow_apply, hu w hw, one_pow]

omit [NumberField K] in

theorem apply_eq_one_of_integral {T : Finset (HeightOneSpectrum (𝓞 L))}
    (hT : ∀ u : UnitPi L, (∀ w ∈ T, u w = 1) → ‖ξhom ξL (unitIdele L u) - 1‖ < 1 / 2)
    (r : (AdeleRing (𝓞 L) L)ˣ) (h1 : (r : AdeleRing (𝓞 L) L).1 = 1)
    (hint : ∀ w : HeightOneSpectrum (𝓞 L), (r : AdeleRing (𝓞 L) L).2 w ∈ w.adicCompletionIntegers L ∧
      ((r⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w ∈ w.adicCompletionIntegers L)
    (hT' : ∀ w ∈ T, (r : AdeleRing (𝓞 L) L).2 w = 1) : ξhom ξL r = 1 := by
  let u : UnitPi L := fun w =>
    ⟨⟨_, (hint w).1⟩, ⟨_, (hint w).2⟩, Subtype.ext (snd_val_mul_inv_apply L r w),
      Subtype.ext (snd_val_inv_mul_apply L r w)⟩
  have hru : unitIdele L u = r := by
    refine Units.ext (Prod.ext ?_ ?_)
    · exact h1.symm
    · exact FiniteAdeleRing.ext L fun w => rfl
  rw [← hru]
  refine apply_unitIdele_eq_one ξL hT u fun w hw => ?_
  exact Units.ext (Subtype.ext (hT' w hw))

end UnitIdeles

omit [NumberField K] in
theorem continuous_arch (hc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ξhom ξL z) :
    Continuous (fun a : (InfiniteAdeleRing L)ˣ =>
        ((ξL ⟨Units.map (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) a,
          Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) := by
  have hinl : Continuous (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) :=
    (continuous_id.prodMk continuous_const :
      Continuous fun x : InfiniteAdeleRing L => (x, (1 : FiniteAdeleRing (𝓞 L) L)))
  exact hc.comp (Continuous.units_map _ hinl)

theorem main
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) :
    Continuous (fun a : (InfiniteAdeleRing L)ˣ =>
        ((ξL ⟨Units.map (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) a,
          Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) ∧
    ∃ R : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ R →
        ∀ u : (L ⊗[K] v.adicCompletion K)ˣ, u ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v →
          TwistedUnipotentTerm.semiLocalCharacter K L ξL v u = 1) ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), R ⊆ S →
        ∀ t : (AdeleRing (𝓞 L) L)ˣ,
          (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
            AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
              AutomorphicForm.TransversalMeasure.integralUnits K L v) →
          ((ξL ⟨t, Subgroup.mem_top t⟩ : ℂˣ) : ℂ) =
            ((ξL ⟨Units.map (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
                (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t),
              Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
            ∏ v ∈ S, TwistedUnipotentTerm.semiLocalCharacter K L ξL v
              (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t) := by
  have hc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ξhom ξL z := hξc
  refine ⟨continuous_arch L ξL hc, ?_⟩
  classical
  obtain ⟨T, hT⟩ := exists_finset_forall_norm_sub_one_lt ξL hc
  refine ⟨T.image (HeightOneSpectrum.under (𝓞 K)), ?_, ?_⟩
  ·
    intro v hv u hu
    rw [semiLocalCharacter_eq]
    have hinv : (idele K L v u)⁻¹ = idele K L v u⁻¹ := (map_inv (idele K L v) u).symm
    refine apply_eq_one_of_integral ξL hT _ (val_idele_fst K L v u) (fun w => ⟨?_, ?_⟩) (fun w hw => ?_)
    · rw [val_idele_snd_apply]
      split_ifs with h
      · exact (coe_semiLocalUnitComponent_mem_of_mem_integralUnits K L v hu ⟨w, h⟩).1
      · exact one_mem _
    · rw [hinv, val_idele_snd_apply]
      split_ifs with h
      · rw [semiLocalUnitComponent_inv]
        exact (coe_semiLocalUnitComponent_mem_of_mem_integralUnits K L v hu ⟨w, h⟩).2
      · exact one_mem _
    · rw [val_idele_snd_apply, dif_neg]
      intro h
      exact hv (Finset.mem_image.2 ⟨w, hw, h⟩)
  ·
    intro S hRS t ht

    set a : (AdeleRing (𝓞 L) L)ˣ := Units.map (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
        (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t) with ha
    set P : (AdeleRing (𝓞 L) L)ˣ :=
      ∏ v ∈ S, idele K L v (TransversalMeasure.semiLocalIdele K L v t) with hP
    set Q : (AdeleRing (𝓞 L) L)ˣ :=
      ∏ v ∈ S, idele K L v (TransversalMeasure.semiLocalIdele K L v t⁻¹) with hQ
    have hPQ : P⁻¹ = Q := by
      rw [hP, hQ, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun v _ => by rw [map_inv, map_inv]
    have hQP : Q⁻¹ = P := by rw [← hPQ, inv_inv]
    set r : (AdeleRing (𝓞 L) L)ˣ := Q * a⁻¹ * t with hr
    have hdec : t = a * P * r := by
      rw [hr, ← hPQ]
      group

    have ha1 : ∀ w : HeightOneSpectrum (𝓞 L), ((a⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w = 1 :=
      fun w => rfl
    have ha2 : ∀ w : HeightOneSpectrum (𝓞 L), (a : AdeleRing (𝓞 L) L).2 w = 1 := fun w => rfl
    have ha3 : ((a⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 =
        ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 := rfl

    have hr2 : ∀ w : HeightOneSpectrum (𝓞 L), (r : AdeleRing (𝓞 L) L).2 w =
        if w.under (𝓞 K) ∈ S then 1 else (t : AdeleRing (𝓞 L) L).2 w := by
      intro w
      rw [hr, snd_val_mul_apply, snd_val_mul_apply, ha1, mul_one, hQ, val_prod_idele_snd_apply]
      split_ifs with h
      · rw [coe_semiLocalUnitComponent_semiLocalIdele]
        exact snd_val_inv_mul_apply L t w
      · exact one_mul _
    have hri2 : ∀ w : HeightOneSpectrum (𝓞 L), ((r⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w =
        if w.under (𝓞 K) ∈ S then 1 else ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w := by
      intro w
      have : r⁻¹ = t⁻¹ * a * P := by rw [hr, mul_inv_rev, mul_inv_rev, inv_inv, hQP, mul_assoc]
      rw [this, snd_val_mul_apply, snd_val_mul_apply, ha2, mul_one, hP, val_prod_idele_snd_apply]
      split_ifs with h
      · rw [coe_semiLocalUnitComponent_semiLocalIdele]
        exact snd_val_inv_mul_apply L t w
      · exact mul_one _
    have hr1 : (r : AdeleRing (𝓞 L) L).1 = 1 := by
      rw [hr, fst_val_mul, fst_val_mul, hQ, val_prod_idele_fst, one_mul, ha3, ← fst_val_mul, inv_mul_cancel]
      rfl

    have hξr : ξhom ξL r = 1 := by
      refine apply_eq_one_of_integral ξL hT r hr1 (fun w => ?_) (fun w hw => ?_)
      · rw [hr2, hri2]
        by_cases h : w.under (𝓞 K) ∈ S
        · rw [if_pos h, if_pos h]
          exact ⟨one_mem _, one_mem _⟩
        · rw [if_neg h, if_neg h]
          have hmem := coe_semiLocalUnitComponent_mem_of_mem_integralUnits K L (w.under (𝓞 K)) (ht _ h) ⟨w, rfl⟩
          rw [← semiLocalUnitComponent_inv, ← map_inv, coe_semiLocalUnitComponent_semiLocalIdele,
            coe_semiLocalUnitComponent_semiLocalIdele] at hmem
          exact hmem
      · rw [hr2, if_pos (hRS (Finset.mem_image_of_mem _ hw))]

    show ξhom ξL t = ξhom ξL a * ∏ v ∈ S, TwistedUnipotentTerm.semiLocalCharacter K L ξL v
      (TransversalMeasure.semiLocalIdele K L v t)
    have hξt : ξhom ξL t = ξhom ξL a * ξhom ξL P * ξhom ξL r := by
      rw [← map_mul, ← map_mul, ← hdec]
    rw [hξt, hξr, mul_one, hP, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun v _ => (semiLocalCharacter_eq K L ξL v _).symm

end TwistedUnipotentTermK7
p2m_reactivate "P2MW.S_NumberField_Idele_exists_finset_forall_semiLocalCharacter_eq_one_and_eq_mul_prod_semiLocalCharacter_of_continuous.TwistedUnipotentTermK7"

end
p2m_reactivate "P2MW.S_NumberField_Idele_exists_finset_forall_semiLocalCharacter_eq_one_and_eq_mul_prod_semiLocalCharacter_of_continuous.TwistedUnipotentTermK7"

open scoped TensorProduct TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) :
    Continuous (fun a : (InfiniteAdeleRing L)ˣ =>
        ((ξL ⟨Units.map (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) a,
          Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) ∧
    ∃ R : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ R →
        ∀ u : (L ⊗[K] v.adicCompletion K)ˣ, u ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v →
          TwistedUnipotentTerm.semiLocalCharacter K L ξL v u = 1) ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), R ⊆ S →
        ∀ t : (AdeleRing (𝓞 L) L)ˣ,
          (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
            AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
              AutomorphicForm.TransversalMeasure.integralUnits K L v) →
          ((ξL ⟨t, Subgroup.mem_top t⟩ : ℂˣ) : ℂ) =
            ((ξL ⟨Units.map (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
                (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t),
              Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
            ∏ v ∈ S, TwistedUnipotentTerm.semiLocalCharacter K L ξL v
              (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t) :=
  TwistedUnipotentTermK7.main K L ξL hξc

end S_NumberField_Idele_exists_finset_forall_semiLocalCharacter_eq_one_and_eq_mul_prod_semiLocalCharacter_of_continuous
end P2MW
export P2MW.S_NumberField_Idele_exists_finset_forall_semiLocalCharacter_eq_one_and_eq_mul_prod_semiLocalCharacter_of_continuous (solution)
