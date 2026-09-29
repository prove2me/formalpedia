-- Prove2me | solution 1 for NumberField.exists_isIdeleClassChar_ne_one_localChar_eq_one_of_mem_range_norm_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7a3f03f1-cc8b-5e72-bec4-293ce366cbf4

import Mathlib
import Definitions.Def_Mathlib_RightActionInstances
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_admissibleModulus_supported
import Theorems.Thm_NumberField_isOpen_range_idelicNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_isIdeleClassChar_ne_one_localChar_eq_one_of_mem_range_norm_of_finrank_eq_two
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain
open NumberField.AdelicLevel NumberField.AdelicVolume
open scoped TensorProduct

noncomputable section

namespace QuadCharExist

section NormBaseChange

variable {K : Type*} [Field K] {L : Type*} [Ring L] [Algebra K L]
variable {A B : Type*} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]

theorem basis_repr_map {ι : Type*} [Fintype ι] (b : Module.Basis ι K L) (φ : A →ₐ[K] B) (T : A ⊗[K] L) (i : ι) :
    (Algebra.TensorProduct.basis B b).repr (Algebra.TensorProduct.map φ (AlgHom.id K L) T) i =
      φ ((Algebra.TensorProduct.basis A b).repr T i) := by
  induction T using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply, map_add]

theorem leftMulMatrix_map {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L) (φ : A →ₐ[K] B)
    (T : A ⊗[K] L) :
    Algebra.leftMulMatrix (Algebra.TensorProduct.basis B b) (Algebra.TensorProduct.map φ (AlgHom.id K L) T) =
      (φ : A →+* B).mapMatrix (Algebra.leftMulMatrix (Algebra.TensorProduct.basis A b) T) := by
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply]
  have : Algebra.TensorProduct.map φ (AlgHom.id K L) T * (1 : B) ⊗ₜ[K] b j =
      Algebra.TensorProduct.map φ (AlgHom.id K L) (T * (1 : A) ⊗ₜ[K] b j) := by
    rw [map_mul, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  rw [this, basis_repr_map]
  rfl

theorem map_norm_eq_norm_map [FiniteDimensional K L] (φ : A →ₐ[K] B) (T : A ⊗[K] L) :
    φ (Algebra.norm A T) = Algebra.norm B (Algebra.TensorProduct.map φ (AlgHom.id K L) T) := by
  classical
  let b := Module.finBasis K L
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis A b),
    Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis B b), leftMulMatrix_map]
  exact RingHom.map_det (φ : A →+* B) _

theorem eq_of_forall_repr_eq {ι : Type*} [Fintype ι] (b : Module.Basis ι K L) {T T' : A ⊗[K] L}
    (h : ∀ i, (Algebra.TensorProduct.basis A b).repr T i = (Algebra.TensorProduct.basis A b).repr T' i) : T = T' :=
  (Algebra.TensorProduct.basis A b).repr.injective (Finsupp.ext h)

end NormBaseChange

section Eval

open scoped Classical

variable (K : Type) [Field K] [NumberField K]

def evF (v : HeightOneSpectrum (𝓞 K)) : AdeleRing (𝓞 K) K →ₐ[K] v.adicCompletion K where
  toRingHom := (finAdeleEval (𝓞 K) K v).comp (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))
  commutes' k := rfl

def evI (w : InfinitePlace K) : AdeleRing (𝓞 K) K →ₐ[K] w.Completion where
  toRingHom := (Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) w).comp
    (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))
  commutes' k := rfl

theorem evF_apply (v : HeightOneSpectrum (𝓞 K)) (x : AdeleRing (𝓞 K) K) : evF K v x = x.2 v := rfl

theorem evI_apply (w : InfinitePlace K) (x : AdeleRing (𝓞 K) K) : evI K w x = x.1 w := rfl

theorem AdeleRing.ext' {x y : AdeleRing (𝓞 K) K} (hI : ∀ w, x.1 w = y.1 w) (hF : ∀ v, x.2 v = y.2 v) : x = y :=
  Prod.ext (funext hI) (FiniteAdeleRing.ext K hF)

def finSingle (v : HeightOneSpectrum (𝓞 K)) (c : v.adicCompletion K) : FiniteAdeleRing (𝓞 K) K :=
  ⟨Pi.single v c, Filter.eventually_cofinite.2 ((Set.finite_singleton v).subset fun w hw => by
    by_contra hwv
    exact hw (by rw [Pi.single_eq_of_ne hwv]; exact zero_mem _))⟩

theorem finSingle_apply_self (v : HeightOneSpectrum (𝓞 K)) (c : v.adicCompletion K) : finSingle K v c v = c := by
  show (Pi.single v c : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K) v = c
  simp

theorem finSingle_apply_of_ne (v : HeightOneSpectrum (𝓞 K)) (c : v.adicCompletion K) {w : HeightOneSpectrum (𝓞 K)}
    (h : w ≠ v) : finSingle K v c w = 0 := by
  show (Pi.single v c : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K) w = 0
  rw [Pi.single_eq_of_ne h]

def inclF (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K →ₗ[K] AdeleRing (𝓞 K) K where
  toFun c := (0, finSingle K v c)
  map_add' c d := AdeleRing.ext' K (fun _ => (add_zero _).symm) fun w => by
    show finSingle K v (c + d) w = finSingle K v c w + finSingle K v d w
    by_cases h : w = v
    · subst h; rw [finSingle_apply_self, finSingle_apply_self, finSingle_apply_self]
    · rw [finSingle_apply_of_ne K v _ h, finSingle_apply_of_ne K v _ h, finSingle_apply_of_ne K v _ h, add_zero]
  map_smul' k c := by
    show ((0 : InfiniteAdeleRing K), finSingle K v (k • c)) = k • ((0 : InfiniteAdeleRing K), finSingle K v c)
    refine Prod.ext ?_ ?_
    · rw [Prod.smul_fst, smul_zero]
    · rw [Prod.smul_snd]
      refine FiniteAdeleRing.ext K fun w => ?_
      rw [Algebra.smul_def k (finSingle K v c)]
      rw [show (algebraMap K (FiniteAdeleRing (𝓞 K) K) k * finSingle K v c) w =
        (algebraMap K (FiniteAdeleRing (𝓞 K) K) k) w * finSingle K v c w from rfl]
      by_cases h : w = v
      · subst h
        rw [finSingle_apply_self, finSingle_apply_self, Algebra.smul_def]
        rfl
      · rw [finSingle_apply_of_ne K v _ h, finSingle_apply_of_ne K v _ h, mul_zero]

theorem evF_inclF_self (v : HeightOneSpectrum (𝓞 K)) (c : v.adicCompletion K) : evF K v (inclF K v c) = c :=
  finSingle_apply_self K v c

theorem evF_inclF_of_ne (v : HeightOneSpectrum (𝓞 K)) (c : v.adicCompletion K) {w : HeightOneSpectrum (𝓞 K)}
    (h : w ≠ v) : evF K w (inclF K v c) = 0 :=
  finSingle_apply_of_ne K v c h

theorem evI_inclF (v : HeightOneSpectrum (𝓞 K)) (c : v.adicCompletion K) (w : InfinitePlace K) :
    evI K w (inclF K v c) = 0 := rfl

def inclI (w : InfinitePlace K) : w.Completion →ₗ[K] AdeleRing (𝓞 K) K :=
  (LinearMap.inl K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp (LinearMap.single K (fun w : InfinitePlace K => w.Completion) w)

theorem evI_inclI_self (w : InfinitePlace K) (c : w.Completion) : evI K w (inclI K w c) = c := by
  show (Pi.single w c : InfiniteAdeleRing K) w = c
  simp

theorem evI_inclI_of_ne (w : InfinitePlace K) (c : w.Completion) {w' : InfinitePlace K} (h : w' ≠ w) :
    evI K w' (inclI K w c) = 0 := by
  show (Pi.single w c : InfiniteAdeleRing K) w' = 0
  rw [Pi.single_eq_of_ne h]

theorem evF_inclI (w : InfinitePlace K) (c : w.Completion) (v : HeightOneSpectrum (𝓞 K)) :
    evF K v (inclI K w c) = 0 := rfl

end Eval

section Tensor

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev TA : Type := AdeleRing (𝓞 K) K ⊗[K] L

variable {K L}

omit [NumberField L] in

theorem map_rTensor {C : Type*} [CommRing C] [Algebra K C] {M : Type*} [AddCommGroup M] [Module K M]
    (φ : AdeleRing (𝓞 K) K →ₐ[K] C) (f : M →ₗ[K] AdeleRing (𝓞 K) K) (y : M ⊗[K] L) :
    Algebra.TensorProduct.map φ (AlgHom.id K L) (LinearMap.rTensor L f y) =
      LinearMap.rTensor L (φ.toLinearMap ∘ₗ f) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c x => rw [LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]; rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]

theorem eq_of_forall_map_ev_eq {T T' : TA K L}
    (hF : ∀ v : HeightOneSpectrum (𝓞 K), Algebra.TensorProduct.map (evF K v) (AlgHom.id K L) T =
      Algebra.TensorProduct.map (evF K v) (AlgHom.id K L) T')
    (hI : ∀ w : InfinitePlace K, Algebra.TensorProduct.map (evI K w) (AlgHom.id K L) T =
      Algebra.TensorProduct.map (evI K w) (AlgHom.id K L) T') : T = T' := by
  let b := Module.finBasis K L
  refine eq_of_forall_repr_eq b fun i => AdeleRing.ext' K (fun w => ?_) (fun v => ?_)
  · have h := congrArg (fun S => (Algebra.TensorProduct.basis (InfinitePlace.Completion w) b).repr S i) (hI w)
    simp only [basis_repr_map] at h
    exact h
  · have h := congrArg (fun S => (Algebra.TensorProduct.basis (v.adicCompletion K) b).repr S i) (hF v)
    simp only [basis_repr_map] at h
    exact h

variable (K L)

abbrev jF (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K ⊗[K] L →ₗ[K] TA K L := LinearMap.rTensor L (inclF K v)

abbrev cF (v : HeightOneSpectrum (𝓞 K)) : TA K L := (1 - inclF K v 1) ⊗ₜ[K] (1 : L)

def TF (v : HeightOneSpectrum (𝓞 K)) (y : v.adicCompletion K ⊗[K] L) : TA K L := jF K L v y + cF K L v

variable {K L}

theorem map_evF_self_TF (v : HeightOneSpectrum (𝓞 K)) (y : v.adicCompletion K ⊗[K] L) :
    Algebra.TensorProduct.map (evF K v) (AlgHom.id K L) (TF K L v y) = y := by
  rw [TF, map_add, map_rTensor, Algebra.TensorProduct.map_tmul, map_sub, map_one, evF_inclF_self, sub_self,
    TensorProduct.zero_tmul, add_zero]
  have : (evF K v).toLinearMap ∘ₗ inclF K v = LinearMap.id := LinearMap.ext fun c => evF_inclF_self K v c
  rw [this, LinearMap.rTensor_id, LinearMap.id_apply]

theorem map_evF_ne_TF (v : HeightOneSpectrum (𝓞 K)) (y : v.adicCompletion K ⊗[K] L) {w : HeightOneSpectrum (𝓞 K)}
    (h : w ≠ v) : Algebra.TensorProduct.map (evF K w) (AlgHom.id K L) (TF K L v y) = 1 := by
  rw [TF, map_add, map_rTensor, Algebra.TensorProduct.map_tmul, map_sub, map_one, evF_inclF_of_ne K v _ h, sub_zero]
  have : (evF K w).toLinearMap ∘ₗ inclF K v = 0 := LinearMap.ext fun c => evF_inclF_of_ne K v c h
  rw [this, LinearMap.rTensor_zero, LinearMap.zero_apply, zero_add]
  rfl

theorem map_evI_TF (v : HeightOneSpectrum (𝓞 K)) (y : v.adicCompletion K ⊗[K] L) (w : InfinitePlace K) :
    Algebra.TensorProduct.map (evI K w) (AlgHom.id K L) (TF K L v y) = 1 := by
  rw [TF, map_add, map_rTensor, Algebra.TensorProduct.map_tmul, map_sub, map_one, evI_inclF, sub_zero]
  have : (evI K w).toLinearMap ∘ₗ inclF K v = 0 := LinearMap.ext fun c => evI_inclF K v c w
  rw [this, LinearMap.rTensor_zero, LinearMap.zero_apply, zero_add]
  rfl

theorem TF_mul_TF (v : HeightOneSpectrum (𝓞 K)) (y y' : v.adicCompletion K ⊗[K] L) :
    TF K L v y * TF K L v y' = TF K L v (y * y') := by
  refine eq_of_forall_map_ev_eq (fun w => ?_) (fun w => ?_)
  · by_cases h : w = v
    · subst h; rw [map_mul, map_evF_self_TF, map_evF_self_TF, map_evF_self_TF]
    · rw [map_mul, map_evF_ne_TF v _ h, map_evF_ne_TF v _ h, map_evF_ne_TF v _ h, mul_one]
  · rw [map_mul, map_evI_TF, map_evI_TF, map_evI_TF, mul_one]

theorem TF_one (v : HeightOneSpectrum (𝓞 K)) : TF K L v 1 = 1 := by
  refine eq_of_forall_map_ev_eq (fun w => ?_) (fun w => ?_)
  · by_cases h : w = v
    · subst h; rw [map_evF_self_TF, map_one]
    · rw [map_evF_ne_TF v _ h, map_one]
  · rw [map_evI_TF, map_one]

variable (K L)

def TFunit (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K ⊗[K] L)ˣ →* (TA K L)ˣ where
  toFun z := ⟨TF K L v z, TF K L v (z⁻¹ : (v.adicCompletion K ⊗[K] L)ˣ),
    by rw [TF_mul_TF, Units.mul_inv, TF_one], by rw [TF_mul_TF, Units.inv_mul, TF_one]⟩
  map_one' := Units.ext (TF_one v)
  map_mul' a b := Units.ext (by simp only [Units.val_mul]; rw [TF_mul_TF])

abbrev jI (w : InfinitePlace K) : w.Completion ⊗[K] L →ₗ[K] TA K L := LinearMap.rTensor L (inclI K w)

abbrev cI (w : InfinitePlace K) : TA K L := (1 - inclI K w 1) ⊗ₜ[K] (1 : L)

def TI (w : InfinitePlace K) (y : w.Completion ⊗[K] L) : TA K L := jI K L w y + cI K L w

variable {K L}

theorem map_evI_self_TI (w : InfinitePlace K) (y : w.Completion ⊗[K] L) :
    Algebra.TensorProduct.map (evI K w) (AlgHom.id K L) (TI K L w y) = y := by
  rw [TI, map_add, map_rTensor, Algebra.TensorProduct.map_tmul, map_sub, map_one, evI_inclI_self, sub_self,
    TensorProduct.zero_tmul, add_zero]
  have : (evI K w).toLinearMap ∘ₗ inclI K w = LinearMap.id := LinearMap.ext fun c => evI_inclI_self K w c
  rw [this, LinearMap.rTensor_id, LinearMap.id_apply]

theorem map_evI_ne_TI (w : InfinitePlace K) (y : w.Completion ⊗[K] L) {w' : InfinitePlace K}
    (h : w' ≠ w) : Algebra.TensorProduct.map (evI K w') (AlgHom.id K L) (TI K L w y) = 1 := by
  rw [TI, map_add, map_rTensor, Algebra.TensorProduct.map_tmul, map_sub, map_one, evI_inclI_of_ne K w _ h, sub_zero]
  have : (evI K w').toLinearMap ∘ₗ inclI K w = 0 := LinearMap.ext fun c => evI_inclI_of_ne K w c h
  rw [this, LinearMap.rTensor_zero, LinearMap.zero_apply, zero_add]
  rfl

theorem map_evF_TI (w : InfinitePlace K) (y : w.Completion ⊗[K] L) (v : HeightOneSpectrum (𝓞 K)) :
    Algebra.TensorProduct.map (evF K v) (AlgHom.id K L) (TI K L w y) = 1 := by
  rw [TI, map_add, map_rTensor, Algebra.TensorProduct.map_tmul, map_sub, map_one, evF_inclI, sub_zero]
  have : (evF K v).toLinearMap ∘ₗ inclI K w = 0 := LinearMap.ext fun c => evF_inclI K w c v
  rw [this, LinearMap.rTensor_zero, LinearMap.zero_apply, zero_add]
  rfl

theorem TI_mul_TI (w : InfinitePlace K) (y y' : w.Completion ⊗[K] L) :
    TI K L w y * TI K L w y' = TI K L w (y * y') := by
  refine eq_of_forall_map_ev_eq (fun v => ?_) (fun w' => ?_)
  · rw [map_mul, map_evF_TI, map_evF_TI, map_evF_TI, mul_one]
  · by_cases h : w' = w
    · subst h; rw [map_mul, map_evI_self_TI, map_evI_self_TI, map_evI_self_TI]
    · rw [map_mul, map_evI_ne_TI w _ h, map_evI_ne_TI w _ h, map_evI_ne_TI w _ h, mul_one]

theorem TI_one (w : InfinitePlace K) : TI K L w 1 = 1 := by
  refine eq_of_forall_map_ev_eq (fun v => ?_) (fun w' => ?_)
  · rw [map_evF_TI, map_one]
  · by_cases h : w' = w
    · subst h; rw [map_evI_self_TI, map_one]
    · rw [map_evI_ne_TI w _ h, map_one]

variable (K L)

def TIunit (w : InfinitePlace K) : (w.Completion ⊗[K] L)ˣ →* (TA K L)ˣ where
  toFun z := ⟨TI K L w z, TI K L w (z⁻¹ : (w.Completion ⊗[K] L)ˣ),
    by rw [TI_mul_TI, Units.mul_inv, TI_one], by rw [TI_mul_TI, Units.inv_mul, TI_one]⟩
  map_one' := Units.ext (TI_one w)
  map_mul' a b := Units.ext (by simp only [Units.val_mul]; rw [TI_mul_TI])

end Tensor

section Norms

open M4aHerbrand M4aHerbrand.GenuineDescent

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def localIdele (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  (Units.map (finIncl (𝓞 K) K)).comp (localUnit (𝓞 K) K v)

theorem val_localIdele_fst (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) (w : InfinitePlace K) :
    ((localIdele K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = 1 := rfl

theorem val_localIdele_snd_self (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    ((localIdele K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = t :=
  localUnit_apply_self (𝓞 K) K v t

theorem val_localIdele_snd_of_ne (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ)
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    ((localIdele K v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1 :=
  localUnit_apply_of_ne (𝓞 K) K v t hw

open scoped Classical in
theorem val_archCentralUnit_fst_self (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    ((archCentralUnit K w a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = a := by
  show Function.update (1 : InfiniteAdeleRing K) w (a : w.Completion) w = a
  rw [Function.update_self]

open scoped Classical in
theorem val_archCentralUnit_fst_of_ne (w : InfinitePlace K) (a : (w.Completion)ˣ) {w' : InfinitePlace K}
    (h : w' ≠ w) : ((archCentralUnit K w a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w' = 1 := by
  show Function.update (1 : InfiniteAdeleRing K) w (a : w.Completion) w' = 1
  rw [Function.update_of_ne h]
  rfl

theorem val_archCentralUnit_snd (w : InfinitePlace K) (a : (w.Completion)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((archCentralUnit K w a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 := rfl

def transport : (TA K L)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  letI := (genuineBaseChange K L).β.toAlgebra
  Units.map ((genuineBaseChange K L).tensorEquiv : TA K L →* AdeleRing (𝓞 L) L)

theorem val_idelicNorm_transport (T : (TA K L)ˣ) :
    (((genuineBaseChange K L).idelicNorm (transport K L T) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) =
      Algebra.norm (AdeleRing (𝓞 K) K) (T : TA K L) := by
  letI := (genuineBaseChange K L).β.toAlgebra
  show (genuineBaseChange K L).adelicNorm ((genuineBaseChange K L).tensorEquiv (T : TA K L)) = _
  exact Algebra.norm_eq_of_algEquiv (genuineBaseChange K L).tensorEquiv (T : TA K L)

theorem localIdele_mem_range_idelicNorm (v : HeightOneSpectrum (𝓞 K)) (z : (v.adicCompletion K ⊗[K] L)ˣ) :
    localIdele K v (Units.map (Algebra.norm (v.adicCompletion K) : v.adicCompletion K ⊗[K] L →* v.adicCompletion K) z) ∈
      (genuineBaseChange K L).idelicNorm.range := by
  refine ⟨transport K L (TFunit K L v z), Units.ext ?_⟩
  rw [val_idelicNorm_transport]
  refine AdeleRing.ext' K (fun w => ?_) (fun w => ?_)
  · rw [val_localIdele_fst, ← evI_apply, map_norm_eq_norm_map]
    show Algebra.norm _ (Algebra.TensorProduct.map (evI K w) (AlgHom.id K L) (TF K L v z)) = 1
    rw [map_evI_TF, map_one]
  · by_cases h : w = v
    · subst h
      rw [val_localIdele_snd_self, ← evF_apply, map_norm_eq_norm_map, Units.coe_map]
      show Algebra.norm _ (Algebra.TensorProduct.map (evF K w) (AlgHom.id K L) (TF K L w z)) = _
      rw [map_evF_self_TF]
    · rw [val_localIdele_snd_of_ne K v _ h, ← evF_apply, map_norm_eq_norm_map]
      show Algebra.norm _ (Algebra.TensorProduct.map (evF K w) (AlgHom.id K L) (TF K L v z)) = 1
      rw [map_evF_ne_TF v _ h, map_one]

theorem archCentralUnit_mem_range_idelicNorm (w : InfinitePlace K) (z : (w.Completion ⊗[K] L)ˣ) :
    archCentralUnit K w (Units.map (Algebra.norm w.Completion : w.Completion ⊗[K] L →* w.Completion) z) ∈
      (genuineBaseChange K L).idelicNorm.range := by
  refine ⟨transport K L (TIunit K L w z), Units.ext ?_⟩
  rw [val_idelicNorm_transport]
  refine AdeleRing.ext' K (fun w' => ?_) (fun v => ?_)
  · by_cases h : w' = w
    · subst h
      rw [val_archCentralUnit_fst_self, ← evI_apply, map_norm_eq_norm_map, Units.coe_map]
      show Algebra.norm _ (Algebra.TensorProduct.map (evI K w') (AlgHom.id K L) (TI K L w' z)) = _
      rw [map_evI_self_TI]
    · rw [val_archCentralUnit_fst_of_ne K w _ h, ← evI_apply, map_norm_eq_norm_map]
      show Algebra.norm _ (Algebra.TensorProduct.map (evI K w') (AlgHom.id K L) (TI K L w z)) = 1
      rw [map_evI_ne_TI w _ h, map_one]
  · rw [val_archCentralUnit_snd, ← evF_apply, map_norm_eq_norm_map]
    show Algebra.norm _ (Algebra.TensorProduct.map (evF K v) (AlgHom.id K L) (TI K L w z)) = 1
    rw [map_evF_TI, map_one]

end Norms

section Character

open HeckeCharacter LanglandsTunnell.P2.Artin M4aHerbrand M4aHerbrand.GenuineDescent NumberField.NormIndex
open scoped IsMulCommutative

theorem exists_injective_monoidHom_units_complex (G : Type*) [Group G] [Finite G] [IsCyclic G] :
    ∃ ψ : G →* ℂˣ, Function.Injective ψ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hn : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  have hn0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (Nat.card G))) (Nat.card G) :=
    Complex.isPrimitiveRoot_exp _ hn0
  have hζ0 : Complex.exp (2 * Real.pi * Complex.I / (Nat.card G)) ≠ 0 := hζ.ne_zero hn0
  have hζu : IsPrimitiveRoot (Units.mk0 _ hζ0) (Nat.card G) := IsPrimitiveRoot.coe_units_iff.mp hζ
  have hord : orderOf (Units.mk0 _ hζ0) ∣ orderOf g := by rw [hn, ← hζu.eq_orderOf]
  refine ⟨monoidHomOfForallMemZpowers hg hord, ?_⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
  rw [map_zpow, monoidHomOfForallMemZpowers_apply_gen] at hx
  have hdvd : ((orderOf (Units.mk0 _ hζ0) : ℕ) : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.mpr hx
  rw [← hζu.eq_orderOf, ← hn] at hdvd
  exact orderOf_dvd_iff_zpow_eq_one.mp hdvd

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] in
theorem admissibleExpOfDegree_ne_zero (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) : admissibleExpOfDegree F n v ≠ 0 := by
  unfold admissibleExpOfDegree; omega

theorem exists_isAdmissibleModulusOfDegree [IsGalois F E] (n : ℕ) :
    ∃ 𝔣 : Ideal (𝓞 F), IsAdmissibleModulusOfDegree F E n 𝔣 := by
  classical
  obtain ⟨𝔣₀, ⟨h0, hram⟩, -⟩ := LanglandsTunnell.P2.Artin.exists_admissibleModulus_supported F E
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ 𝔣₀}.Finite := Ideal.finite_factors h0
  refine ⟨𝔣₀ ^ hfin.toFinset.sup (fun v => admissibleExpOfDegree F n v), pow_ne_zero _ h0, fun v hv => ?_⟩
  have hdvd : v.asIdeal ∣ 𝔣₀ := (dvd_pow_self v.asIdeal (by unfold admissibleExp; omega)).trans (hram v hv)
  have hle : admissibleExpOfDegree F n v ≤ hfin.toFinset.sup (fun v => admissibleExpOfDegree F n v) :=
    Finset.le_sup (f := fun v => admissibleExpOfDegree F n v) (hfin.mem_toFinset.mpr hdvd)
  exact (pow_dvd_pow v.asIdeal hle).trans (pow_dvd_pow_of_dvd hdvd _)

end Character

open scoped TensorProduct.RightActions in
theorem main (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) :
    ∃ η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
      IsIdeleClassChar (𝓞 K) K η ∧ Continuous η ∧ η ≠ 1 ∧ (∀ x : (AdeleRing (𝓞 K) K)ˣ, η x ^ 2 = 1) ∧
      (∀ (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ),
        x ∈ (Units.map (Algebra.norm (v.adicCompletion K) :
            L ⊗[K] v.adicCompletion K →* v.adicCompletion K)).range →
          localChar η v x = 1) ∧
      (∀ (w : InfinitePlace K) (x : (w.Completion)ˣ),
        x ∈ (Units.map (Algebra.norm w.Completion : L ⊗[K] w.Completion →* w.Completion)).range →
          archLocalChar η w x = 1) := by
  classical
  haveI hq : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  haveI : IsGalois K L := inferInstance
  haveI : IsMulCommutative (L ≃ₐ[K] L) := inferInstance
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans h2

  obtain ⟨𝔣, hadm⟩ := exists_isAdmissibleModulusOfDegree K L (Module.finrank K L)
  obtain ⟨r, hprinc, hker, hsurj, -⟩ :=
    NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
      K L 𝔣 hadm

  obtain ⟨ψ, hψ⟩ := exists_injective_monoidHom_units_complex (L ≃ₐ[K] L)
  have hnorm : ∀ u : (AdeleRing (𝓞 K) K)ˣ,
      u ∈ (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range → ψ (r u) = 1 := by
    intro u hu
    have : u ∈ r.ker := by rw [hker]; exact Subgroup.mem_sup_right hu
    rw [MonoidHom.mem_ker] at this
    rw [this, map_one]
  refine ⟨ψ.comp r, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro u
    have hu : r (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 1 := hprinc ⟨u, rfl⟩
    exact (congrArg ψ hu).trans (map_one ψ)
  ·
    have hopen : IsOpen ((r.ker : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) := by
      refine Subgroup.isOpen_mono ?_
        (NumberField.isOpen_range_idelicNorm K L (M4aHerbrand.GenuineDescent.genuineBaseChange K L))
      rw [hker]; exact le_sup_right
    refine continuous_of_continuousAt_one (ψ.comp r) ?_
    have hev : (⇑(ψ.comp r)) =ᶠ[nhds 1] fun _ => (1 : ℂˣ) := by
      filter_upwards [hopen.mem_nhds (one_mem r.ker)] with x hx
      have hx' : r x = 1 := hx
      show ψ (r x) = 1
      rw [hx', map_one]
    exact continuousAt_const.congr hev.symm
  ·
    haveI : Nontrivial (L ≃ₐ[K] L) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
    obtain ⟨g, hg⟩ := exists_ne (1 : L ≃ₐ[K] L)
    obtain ⟨x, hx⟩ := hsurj g
    intro h
    have h1 : ψ (r x) = 1 := by
      have := DFunLike.congr_fun h x
      exact this
    rw [hx, ← map_one ψ] at h1
    exact hg (hψ h1)
  ·
    intro x
    show ψ (r x) ^ 2 = 1
    rw [← map_pow, ← hcard, pow_card_eq_one', map_one]
  ·
    intro v x hx
    obtain ⟨z, rfl⟩ := hx
    set e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] v.adicCompletion K ⊗[K] L :=
      (TensorProduct.RightActions.Algebra.TensorProduct.comm K (v.adicCompletion K) L).symm with he
    have hzz : Units.map (Algebra.norm (v.adicCompletion K) : L ⊗[K] v.adicCompletion K →* v.adicCompletion K) z =
        Units.map (Algebra.norm (v.adicCompletion K) : v.adicCompletion K ⊗[K] L →* v.adicCompletion K)
          (Units.map (e : L ⊗[K] v.adicCompletion K →* v.adicCompletion K ⊗[K] L) z) := by
      refine Units.ext ?_
      simp only [Units.coe_map]
      exact (Algebra.norm_eq_of_algEquiv e (z : L ⊗[K] v.adicCompletion K)).symm
    show ψ (r (localIdele K v _)) = 1
    rw [hzz]
    exact hnorm _ (localIdele_mem_range_idelicNorm K L v _)
  ·
    intro w x hx
    obtain ⟨z, rfl⟩ := hx
    set e : L ⊗[K] w.Completion ≃ₐ[w.Completion] w.Completion ⊗[K] L :=
      (TensorProduct.RightActions.Algebra.TensorProduct.comm K w.Completion L).symm with he
    have hzz : Units.map (Algebra.norm w.Completion : L ⊗[K] w.Completion →* w.Completion) z =
        Units.map (Algebra.norm w.Completion : w.Completion ⊗[K] L →* w.Completion)
          (Units.map (e : L ⊗[K] w.Completion →* w.Completion ⊗[K] L) z) := by
      refine Units.ext ?_
      simp only [Units.coe_map]
      exact (Algebra.norm_eq_of_algEquiv e (z : L ⊗[K] w.Completion)).symm
    show ψ (r (archCentralUnit K w _)) = 1
    rw [hzz]
    exact hnorm _ (archCentralUnit_mem_range_idelicNorm K L w _)

end QuadCharExist

end

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain in
open scoped TensorProduct TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) :
    ∃ η : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
      IsIdeleClassChar (𝓞 K) K η ∧ Continuous η ∧ η ≠ 1 ∧ (∀ x : (AdeleRing (𝓞 K) K)ˣ, η x ^ 2 = 1) ∧
      (∀ (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ),
        x ∈ (Units.map (Algebra.norm (v.adicCompletion K) :
            L ⊗[K] v.adicCompletion K →* v.adicCompletion K)).range →
          localChar η v x = 1) ∧
      (∀ (w : InfinitePlace K) (x : (w.Completion)ˣ),
        x ∈ (Units.map (Algebra.norm w.Completion : L ⊗[K] w.Completion →* w.Completion)).range →
          archLocalChar η w x = 1) :=
  QuadCharExist.main K L h2

end S_NumberField_exists_isIdeleClassChar_ne_one_localChar_eq_one_of_mem_range_norm_of_finrank_eq_two
end P2MW
export P2MW.S_NumberField_exists_isIdeleClassChar_ne_one_localChar_eq_one_of_mem_range_norm_of_finrank_eq_two (solution)
