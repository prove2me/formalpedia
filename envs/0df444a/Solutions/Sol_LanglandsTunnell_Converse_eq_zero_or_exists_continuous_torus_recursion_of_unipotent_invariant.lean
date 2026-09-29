-- Prove2me | solution 1 for LanglandsTunnell.Converse.eq_zero_or_exists_continuous_torus_recursion_of_unipotent_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e034101e-6afa-5248-a30b-4c1f3a002c58

import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem
import Theorems.Thm_AdelicDock_finEmbed_localEmbed_mem_levelOne_inf_finiteAdelicGL2Subgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_eq_zero_or_exists_continuous_torus_recursion_of_unipotent_invariant
p2m_attr_erase "instance" "NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.SmoothCusp
open AdelicDock HeckeIntegralSeam LocalGL2
open IsDedekindDomain NumberField

noncomputable section

namespace RowCDev

variable (K : Type) [Field K] [NumberField K]

private def rc_torus (t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ) : AdelicGL2 (𝓞 K) K :=
  diagOne (t₁ * t₂⁻¹) * centralScalar (𝓞 K) K t₂

private theorem rc_centralScalar_coe (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((centralScalar (𝓞 K) K z : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
      = Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 K) K) := rfl

private theorem rc_centralScalar_commute (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    Commute (centralScalar (𝓞 K) K z) g := by
  show centralScalar (𝓞 K) K z * g = g * centralScalar (𝓞 K) K z
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, rc_centralScalar_coe, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact mul_comm _ _

private theorem rc_torus_mul (a b c d : (AdeleRing (𝓞 K) K)ˣ) :
    rc_torus K (a * c) (b * d) = rc_torus K a b * rc_torus K c d := by
  unfold rc_torus
  rw [show a * c * (b * d)⁻¹ = a * b⁻¹ * (c * d⁻¹) by rw [mul_inv, mul_mul_mul_comm],
    map_mul (diagOne (A := AdeleRing (𝓞 K) K)), map_mul (centralScalar (𝓞 K) K)]
  exact Commute.mul_mul_mul_comm (rc_centralScalar_commute K b (diagOne (c * d⁻¹))).symm _ _

private theorem rc_torus_one_one : rc_torus K 1 1 = 1 := by
  simp [rc_torus]

private theorem rc_torus_coe (t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ) :
    ((rc_torus K t₁ t₂ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
      = !![(t₁ : AdeleRing (𝓞 K) K), 0; 0, (t₂ : AdeleRing (𝓞 K) K)] := by
  ext i j
  simp only [rc_torus, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, diagOne_coe_apply, rc_centralScalar_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem rc_torus_mul_unipotent (t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ) (x : AdeleRing (𝓞 K) K) :
    rc_torus K t₁ t₂ * unipotentGL2 x
      = unipotentGL2 ((t₁ : AdeleRing (𝓞 K) K) * x * ((t₂⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))
          * rc_torus K t₁ t₂ := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, rc_torus_coe, unipotentGL2_coe, Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp

private theorem rc_torus_mul_diagOne (t₁ t₂ ϖ : (AdeleRing (𝓞 K) K)ˣ) :
    rc_torus K t₁ t₂ * diagOne ϖ = rc_torus K (ϖ * t₁) t₂ := by
  have h : rc_torus K ϖ 1 = diagOne ϖ := by simp [rc_torus]
  rw [← h, ← rc_torus_mul, mul_comm t₁ ϖ, mul_one]

private theorem rc_torus_mul_torus_one (t₁ t₂ ϖ : (AdeleRing (𝓞 K) K)ˣ) :
    rc_torus K t₁ t₂ * rc_torus K 1 ϖ = rc_torus K t₁ (ϖ * t₂) := by
  rw [← rc_torus_mul, mul_one, mul_comm t₂ ϖ]

private theorem rc_centralScalar_mul_torus (z t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ) :
    centralScalar (𝓞 K) K z * rc_torus K t₁ t₂ = rc_torus K (z * t₁) (z * t₂) := by
  rw [rc_torus_mul]
  congr 1
  simp [rc_torus]

private theorem rc_det_diagOne (a : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (diagOne a : AdelicGL2 (𝓞 K) K) = a := by
  apply Units.ext
  show (Matrix.diagonal ![(a : AdeleRing (𝓞 K) K), 1]).det = (a : AdeleRing (𝓞 K) K)
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

private theorem rc_det_heckeGen (v : HeightOneSpectrum (𝓞 K)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v) = uniformizerIdele K v :=
  rc_det_diagOne K (uniformizerIdele K v)

private theorem rc_continuous_diagOne :
    Continuous (fun a : (AdeleRing (𝓞 K) K)ˣ => (diagOne a : AdelicGL2 (𝓞 K) K)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun a : (AdeleRing (𝓞 K) K)ˣ => Matrix.diagonal ![(a : AdeleRing (𝓞 K) K), 1]
    refine Continuous.matrix_diagonal ?_
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact Units.continuous_val
    · exact continuous_const
  · show Continuous fun a : (AdeleRing (𝓞 K) K)ˣ =>
      Matrix.diagonal ![((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K), 1]
    refine Continuous.matrix_diagonal ?_
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact Units.continuous_coe_inv
    · exact continuous_const

private theorem rc_continuous_centralScalar : Continuous (centralScalar (𝓞 K) K) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => Matrix.diagonal fun _ : Fin 2 => (z : AdeleRing (𝓞 K) K)
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val)
  · show Continuous fun z : (AdeleRing (𝓞 K) K)ˣ =>
      Matrix.diagonal fun _ : Fin 2 => ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_coe_inv)

private theorem rc_continuous_torus :
    Continuous fun t : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ => rc_torus K t.1 t.2 := by
  unfold rc_torus
  exact ((rc_continuous_diagOne K).comp (continuous_fst.mul continuous_snd.inv)).mul
    ((rc_continuous_centralScalar K).comp continuous_snd)

private def rc_borelDiag (γ₁ γ₂ : Kˣ) : Matrix.GeneralLinearGroup (Fin 2) K :=
  diagOne (γ₁ * γ₂⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin 2) γ₂

omit [NumberField K] in
private theorem rc_borelDiag_coe (γ₁ γ₂ : Kˣ) :
    ((rc_borelDiag K γ₁ γ₂ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = !![(γ₁ : K), 0; 0, (γ₂ : K)] := by
  ext i j
  simp only [rc_borelDiag, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

omit [NumberField K] in
private theorem rc_borelDiag_mem (γ₁ γ₂ : Kˣ) : rc_borelDiag K γ₁ γ₂ ∈ borelSubgroup K := by
  show ((rc_borelDiag K γ₁ γ₂ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  rw [rc_borelDiag_coe]
  simp

private theorem rc_globalPoints_borelDiag (γ₁ γ₂ : Kˣ) :
    globalPoints (𝓞 K) K (rc_borelDiag K γ₁ γ₂)
      = rc_torus K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) γ₁)
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) γ₂) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [rc_torus_coe]
  show (((rc_borelDiag K γ₁ γ₂ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map
      (algebraMap K (AdeleRing (𝓞 K) K))) i j = _
  rw [rc_borelDiag_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem rc_torus_kinv (ϕ : AdelicGL2 (𝓞 K) K → ℂ)
    (hborel : ∀ γ ∈ borelSubgroup K, ∀ g : AdelicGL2 (𝓞 K) K, ϕ (globalPoints (𝓞 K) K γ * g) = ϕ g)
    (g₀ : AdelicGL2 (𝓞 K) K) (γ₁ γ₂ : Kˣ) (t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ) :
    ϕ (rc_torus K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) γ₁ * t₁)
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) γ₂ * t₂) * g₀) = ϕ (rc_torus K t₁ t₂ * g₀) := by
  rw [rc_torus_mul, ← rc_globalPoints_borelDiag, mul_assoc]
  exact hborel _ (rc_borelDiag_mem K γ₁ γ₂) _

private theorem rc_torus_recB (Pi : HeckeEigensystem K ℂ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ϕ : AdelicGL2 (𝓞 K) K → ℂ)
    (hcentralEigen : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
      ϕ (centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) * g)
        = (HeckeEigensystem.cNorm v)⁻¹ * Pi.b v * ϕ g)
    (g₀ : AdelicGL2 (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) (t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ) :
    ϕ (rc_torus K (uniformizerIdele K v * t₁) (uniformizerIdele K v * t₂) * g₀)
      = (HeckeEigensystem.cNorm v)⁻¹ * Pi.b v * ϕ (rc_torus K t₁ t₂ * g₀) := by
  have h := hcentralEigen v hv (rc_torus K t₁ t₂ * g₀)
  rw [rc_det_heckeGen, ← mul_assoc, rc_centralScalar_mul_torus] at h
  exact h

private def rc_comp (g : AdelicGL2 (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K) :=
  finComponent (𝓞 K) K v (glFin (𝓞 K) K g)

private def rc_badSet (g : AdelicGL2 (𝓞 K) K) : Set (HeightOneSpectrum (𝓞 K)) :=
  {v | rc_comp K g v ∉ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)}

private theorem rc_entry_finite (a : FiniteAdeleRing (𝓞 K) K) :
    {w : HeightOneSpectrum (𝓞 K) | a w ∉ w.adicCompletionIntegers K}.Finite :=
  Filter.eventually_cofinite.mp a.2

private theorem rc_badSet_finite (g : AdelicGL2 (𝓞 K) K) : (rc_badSet K g).Finite := by
  classical
  have hfin : (⋃ i : Fin 2, ⋃ j : Fin 2,
      ({w : HeightOneSpectrum (𝓞 K) |
          ((glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) w
            ∉ w.adicCompletionIntegers K} ∪
        {w : HeightOneSpectrum (𝓞 K) |
          (((glFin (𝓞 K) K g)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j w
            ∉ w.adicCompletionIntegers K})).Finite :=
    Set.finite_iUnion fun i => Set.finite_iUnion fun j => (rc_entry_finite K _).union (rc_entry_finite K _)
  refine hfin.subset ?_
  intro v hv
  by_contra hv'
  simp only [Set.mem_iUnion, Set.mem_union, Set.mem_setOf_eq, not_exists, not_or, not_not] at hv'
  apply hv
  have hinv : (rc_comp K g v)⁻¹ = finComponent (𝓞 K) K v ((glFin (𝓞 K) K g)⁻¹) :=
    (map_inv (finComponent (𝓞 K) K v) (glFin (𝓞 K) K g)).symm
  rw [FLT.SpectralSide.mem_integralSubgroup_iff_entries_mem (R := v.adicCompletionIntegers K)
    (K := v.adicCompletion K) (fun _ _ hab => Subtype.ext hab)]
  refine ⟨fun i j => ⟨⟨_, (hv' i j).1⟩, rfl⟩, fun i j => ?_⟩
  rw [hinv]
  exact ⟨⟨_, (hv' i j).2⟩, rfl⟩

private theorem rc_eq_of_components {x y : AdelicGL2 (𝓞 K) K} (harch : glArch (𝓞 K) K x = glArch (𝓞 K) K y)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 K),
      finComponent (𝓞 K) K w (glFin (𝓞 K) K x) = finComponent (𝓞 K) K w (glFin (𝓞 K) K y)) :
    x = y := by
  apply Units.ext
  apply matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 K) K
  · exact congrArg Units.val harch
  · apply matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 K) K
    intro w
    exact congrArg Units.val (hfin w)

private theorem rc_commute_of_comp_eq_one {h : AdelicGL2 (𝓞 K) K} (v : HeightOneSpectrum (𝓞 K))
    (hh : finComponent (𝓞 K) K v (glFin (𝓞 K) K h) = 1)
    (r : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K)) :
    h * finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v r) = finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v r) * h := by
  apply rc_eq_of_components
  · simp only [map_mul, glArch_finEmbed, mul_one, one_mul]
  · intro w
    simp only [map_mul, glFin_finEmbed]
    by_cases hw : w = v
    · subst hw
      rw [finComponent_localEmbed_self, hh, one_mul, mul_one]
    · rw [finComponent_localEmbed_of_ne (𝓞 K) K v r hw, one_mul, mul_one]

private theorem rc_comp_base_eq_one (g₀ : AdelicGL2 (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    finComponent (𝓞 K) K v (glFin (𝓞 K) K
      (g₀ * (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v (rc_comp K g₀ v)))⁻¹)) = 1 := by
  simp only [map_mul, map_inv, glFin_finEmbed, finComponent_localEmbed_self, rc_comp, mul_inv_cancel]

private theorem rc_isHeckeCosetSystem_comp_equiv {G : Type*} [Group G] {U : Subgroup G} {g : G} {ι κ : Type*}
    {reps : ι → G} (h : IsHeckeCosetSystem U g reps) (e : κ ≃ ι) :
    IsHeckeCosetSystem U g (reps ∘ e) where
  mem_doubleCoset i := h.mem_doubleCoset (e i)
  covers x hx := by
    obtain ⟨i, hi⟩ := h.covers x hx
    exact ⟨e.symm i, by simpa using hi⟩
  mk_injective a b hab := e.injective (h.mk_injective hab)

private theorem rc_card_residue (v : HeightOneSpectrum (𝓞 K)) [Fintype (𝓞 K ⧸ v.asIdeal)] :
    Fintype.card (𝓞 K ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

private def rc_optionEquivFin (v : HeightOneSpectrum (𝓞 K)) [Fintype (𝓞 K ⧸ v.asIdeal)] :
    Option (𝓞 K ⧸ v.asIdeal) ≃ Fin (Ideal.absNorm v.asIdeal + 1) :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_option, rc_card_residue])

private theorem rc_exists_embed_unipotentInt_eq (v : HeightOneSpectrum (𝓞 K)) (b : v.adicCompletionIntegers K) :
    ∃ x : AdeleRing (𝓞 K) K,
      finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v (unipotentInt (v.adicCompletion K) b)) = unipotentGL2 x := by
  classical
  refine ⟨((0 : InfiniteAdeleRing K),
    splice (𝓞 K) K v 0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) b)), ?_⟩
  apply Units.ext
  apply matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 K) K
  · rw [coe_finEmbed, mapMatrix_arch_finMat, unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply, adeleArch_apply] <;> rfl
  · rw [coe_finEmbed, mapMatrix_fin_finMat, coe_localEmbed, unipotentGL2_coe]
    apply matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 K) K
    intro w
    by_cases hw : w = v
    · subst hw
      rw [mapMatrix_localMat_self, coe_unipotentInt]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply, finAdeleEval_apply, adeleFin_apply] <;> rfl
    · rw [mapMatrix_localMat_of_ne (𝓞 K) K v _ hw]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [RingHom.mapMatrix_apply, finAdeleEval_apply, adeleFin_apply, splice_apply_of_ne (𝓞 K) K v _ _ hw,
          coe_zero_apply] <;> rfl

private theorem rc_embed_localRepInf_eq (v : HeightOneSpectrum (𝓞 K)) (ϖ : v.adicCompletionIntegers K)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hdiag : finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v (diagPi ϖ hϖ0)) = heckeGen (𝓞 K) K v) :
    finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v (localRepInf ϖ hϖ0)) = rc_torus K 1 (uniformizerIdele K v) := by
  classical

  have hϖ : ((uniformizerIdele K v : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
      = ((finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v (diagPi ϖ hϖ0)) : AdelicGL2 (𝓞 K) K) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 := by
    rw [hdiag]
    show _ = (Matrix.diagonal ![((uniformizerIdele K v : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K), 1]) 0 0
    simp
  apply Units.ext
  rw [rc_torus_coe, Units.val_one, hϖ, coe_finEmbed, coe_finEmbed, coe_localEmbed, coe_localEmbed]
  apply matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 K) K
  · rw [mapMatrix_arch_finMat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [RingHom.mapMatrix_apply, finMat, adeleArch_apply, Matrix.one_fin_two] <;> rfl
  · rw [mapMatrix_fin_finMat]
    apply matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 K) K
    intro w
    by_cases hw : w = v
    · subst hw
      rw [mapMatrix_localMat_self, coe_localRepInf]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [RingHom.mapMatrix_apply, finMat, finAdeleEval_apply, adeleFin_apply, localMat_apply_self, coe_diagPi]
          <;> rfl
    · rw [mapMatrix_localMat_of_ne (𝓞 K) K v _ hw]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [RingHom.mapMatrix_apply, finMat, finAdeleEval_apply, adeleFin_apply,
          localMat_apply_of_ne (𝓞 K) K v _ _ _ hw, Matrix.one_fin_two] <;> rfl

private theorem rc_torus_recA (Pi : HeckeEigensystem K ℂ) (S : Finset (HeightOneSpectrum (𝓞 K))) (N : Ideal (𝓞 K))
    (ϕ : AdelicGL2 (𝓞 K) K → ℂ)
    (hunip : ∀ (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), ϕ (unipotentGL2 x * g) = ϕ g)
    (hlevel : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      ϕ (g * u) = ϕ g)
    (heigen : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (heckeGen (𝓞 K) K v) v ϕ (Pi.a v))
    (g₀ : AdelicGL2 (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) (hvS : v ∉ S) (hvN : ¬ v.asIdeal ∣ N)
    (hvg : rc_comp K g₀ v ∈ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
    (t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ) :
    HeckeEigensystem.cNorm v * ϕ (rc_torus K (uniformizerIdele K v * t₁) t₂ * g₀)
        + ϕ (rc_torus K t₁ (uniformizerIdele K v * t₂) * g₀)
      = Pi.a v * ϕ (rc_torus K t₁ t₂ * g₀) := by
  classical
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  haveI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  obtain ⟨ϖ, hϖ0, -, hdiag, sec, -, hsys⟩ :=
    HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen K v
  set reps : Option (𝓞 K ⧸ v.asIdeal) → AdelicGL2 (𝓞 K) K := fun i =>
    finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v (i.elim (localRepInf ϖ hϖ0)
      (fun c => localRepSome ϖ hϖ0 (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c))))) with hreps
  have hsysO : IsHeckeCosetSystem (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (heckeGen (𝓞 K) K v) reps :=
    hsys N hvN
  obtain ⟨repsF, hsysF, heq⟩ := heigen v hvS

  set u : AdelicGL2 (𝓞 K) K := finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v (rc_comp K g₀ v)) with hu_def
  have hu : u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K :=
    AdelicDock.finEmbed_localEmbed_mem_levelOne_inf_finiteAdelicGL2Subgroup K v hvN hvg
  set h : AdelicGL2 (𝓞 K) K := g₀ * u⁻¹ with hh_def
  have hhv : finComponent (𝓞 K) K v (glFin (𝓞 K) K h) = 1 := rc_comp_base_eq_one K g₀ v
  have hϕh : ∀ x : AdelicGL2 (𝓞 K) K, ϕ (x * h) = ϕ (x * g₀) := by
    intro x
    rw [hh_def, ← mul_assoc]
    exact hlevel _ _ (inv_mem hu)

  have hcomm : ∀ i, h * reps i = reps i * h := fun i => rc_commute_of_comp_eq_one K v hhv _

  have e := rc_optionEquivFin K v
  have key := HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hsysF
    (rc_isHeckeCosetSystem_comp_equiv hsysO e.symm) hlevel (rc_torus K t₁ t₂ * h)
  have hright : ∑ i, ϕ (rc_torus K t₁ t₂ * h * repsF i) = Pi.a v * ϕ (rc_torus K t₁ t₂ * g₀) := by
    have h1 := heq (rc_torus K t₁ t₂ * h)
    rw [hϕh] at h1
    exact h1
  have hleft : ∑ i, ϕ (rc_torus K t₁ t₂ * h * (reps ∘ e.symm) i) = ∑ j, ϕ (rc_torus K t₁ t₂ * h * reps j) :=
    Equiv.sum_comp e.symm (fun j => ϕ (rc_torus K t₁ t₂ * h * reps j))
  rw [hleft, hright] at key
  have hsum : ∑ j, ϕ (rc_torus K t₁ t₂ * h * reps j)
      = ϕ (rc_torus K t₁ t₂ * h * reps none) + ∑ c, ϕ (rc_torus K t₁ t₂ * h * reps (some c)) :=
    Fintype.sum_option _
  rw [hsum] at key

  have hnone : ϕ (rc_torus K t₁ t₂ * h * reps none) = ϕ (rc_torus K t₁ (uniformizerIdele K v * t₂) * g₀) := by
    have h0 : reps none = finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v (localRepInf ϖ hϖ0)) := rfl
    rw [mul_assoc, hcomm, ← mul_assoc, hϕh, h0, rc_embed_localRepInf_eq K v ϖ hϖ0 hdiag, rc_torus_mul_torus_one]

  have hsome : ∀ c : 𝓞 K ⧸ v.asIdeal,
      ϕ (rc_torus K t₁ t₂ * h * reps (some c)) = ϕ (rc_torus K (uniformizerIdele K v * t₁) t₂ * g₀) := by
    intro c
    have h0 : reps (some c) = finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v
        (unipotentInt (v.adicCompletion K) (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c))
          * diagPi ϖ hϖ0)) := rfl
    obtain ⟨x, hx⟩ := rc_exists_embed_unipotentInt_eq K v (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c))
    rw [mul_assoc, hcomm, ← mul_assoc, hϕh, h0, map_mul, map_mul, hx, hdiag, ← mul_assoc, rc_torus_mul_unipotent,
      mul_assoc, mul_assoc, hunip, ← mul_assoc]

    exact congrArg ϕ (congrArg (· * g₀) (rc_torus_mul_diagOne K t₁ t₂ (uniformizerIdele K v)))
  rw [hnone, Finset.sum_congr rfl (fun c _ => hsome c), Finset.sum_const, Finset.card_univ, rc_card_residue,
    nsmul_eq_mul] at key
  rw [add_comm]
  exact key

private theorem rc_finite_dvd (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ N}.Finite :=
  Ideal.finite_factors hN

private theorem rc_exists_place_comap_eq (p : ℕ) (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), v.asIdeal.comap (algebraMap ℤ (𝓞 K)) = Ideal.span {(p : ℤ)} := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp hp)
  have hinj : Function.Injective (algebraMap ℤ (𝓞 K)) := by
    rw [algebraMap_int_eq]
    exact Int.cast_injective
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {(p : ℤ)}) (⊥ : Ideal (𝓞 K))
    (by rw [Ideal.comap_bot_of_injective (f := algebraMap ℤ (𝓞 K)) hinj]; exact bot_le)
  refine ⟨⟨Q, hQ, ?_⟩, hQP⟩
  rintro rfl
  rw [Ideal.comap_bot_of_injective (f := algebraMap ℤ (𝓞 K)) hinj] at hQP
  exact hp0 (Ideal.span_singleton_eq_bot.mp hQP.symm)

private theorem rc_exists_place_notMem
    (S : Finset (HeightOneSpectrum (𝓞 K))) : ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S := by
  classical
  choose f hf using fun p : Nat.Primes => rc_exists_place_comap_eq K p.1 p.2
  have hinj : Function.Injective f := by
    intro p q hpq
    have h : Ideal.span {(p.1 : ℤ)} = Ideal.span {(q.1 : ℤ)} := by rw [← hf p, ← hf q, hpq]
    have hmem : (p.1 : ℤ) ∈ Ideal.span {(q.1 : ℤ)} := by
      rw [← h]
      exact Ideal.mem_span_singleton_self _
    have hdvd : q.1 ∣ p.1 := Int.natCast_dvd_natCast.mp (Ideal.mem_span_singleton.mp hmem)
    exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp hdvd).symm
  obtain ⟨v, -, hv⟩ := (Set.infinite_range_of_injective hinj).exists_notMem_finset S
  exact ⟨v, hv⟩

private def rc_LowerRowOne (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 K), m 1 0 w = 0 ∧ m 1 1 w = 1

private theorem rc_lowerRow_mul {A : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)} (hA : rc_LowerRowOne K A)
    (B : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) (w : HeightOneSpectrum (𝓞 K)) :
    (A * B) 1 0 w = B 1 0 w ∧ (A * B) 1 1 w = B 1 1 w := by
  obtain ⟨h0, h1⟩ := hA w
  constructor <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, coe_add_apply, coe_mul_apply, h0, h1, zero_mul, one_mul, zero_add]

private theorem rc_lowerRowOne_mul {A B : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)} (hA : rc_LowerRowOne K A)
    (hB : rc_LowerRowOne K B) : rc_LowerRowOne K (A * B) := by
  intro w
  rw [(rc_lowerRow_mul K hA B w).1, (rc_lowerRow_mul K hA B w).2]
  exact hB w

private theorem rc_lowerRowOne_inv {g : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hg : rc_LowerRowOne K (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) :
    rc_LowerRowOne K ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := by
  intro w
  have h := rc_lowerRow_mul K hg ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) w
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one] at h
  rw [← h.1, ← h.2]
  simp [coe_zero_apply, coe_one_apply]

private theorem rc_glFin_entry (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
      = adeleFin (𝓞 K) K ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) := rfl

private theorem rc_lowerRowOne_glFin_diagOne (a : (AdeleRing (𝓞 K) K)ˣ) :
    rc_LowerRowOne K (glFin (𝓞 K) K (diagOne a) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := by
  intro w
  rw [rc_glFin_entry, rc_glFin_entry, diagOne_coe_apply, diagOne_coe_apply]
  simp [coe_zero_apply, coe_one_apply]

private theorem rc_eq_zero_of_mem_idealBall_bot {x : FiniteAdeleRing (𝓞 K) K} (hx : x ∈ idealBall (𝓞 K) K ⊥)
    (w : HeightOneSpectrum (𝓞 K)) : x w = 0 := by
  have h : Valued.v (x w) ≤ idealBound (𝓞 K) ⊥ w := hx w
  rw [idealBound_bot] at h
  exact (Valuation.zero_iff _).mp (le_antisymm h zero_le')

private theorem rc_mem_idealBall_of_forall_eq_zero
    {x : FiniteAdeleRing (𝓞 K) K} (hx : ∀ w, x w = 0) (N : Ideal (𝓞 K)) :
    x ∈ idealBall (𝓞 K) K N :=
  fun w => by rw [hx w, map_zero]; exact zero_le'

private theorem rc_lowerRowOne_of_mem_levelBot {u : AdelicGL2 (𝓞 K) K}
    (hu : u ∈ levelOne (𝓞 K) K ⊥ ⊓ finiteAdelicGL2Subgroup K) :
    rc_LowerRowOne K (glFin (𝓞 K) K u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := by
  have h := (Subgroup.mem_inf.mp hu).1
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at h
  intro w
  refine ⟨rc_eq_zero_of_mem_idealBall_bot K h.1.lowerLeft w, ?_⟩
  have h11 := rc_eq_zero_of_mem_idealBall_bot K h.1.lowerRight w
  rw [coe_sub_apply, coe_one_apply, sub_eq_zero] at h11
  exact h11

private theorem rc_levelBot_le_levelTop :
    levelOne (𝓞 K) K ⊥ ⊓ finiteAdelicGL2Subgroup K ≤ levelOne (𝓞 K) K ⊤ ⊓ finiteAdelicGL2Subgroup K := by
  intro u hu
  refine Subgroup.mem_inf.mpr ⟨?_, (Subgroup.mem_inf.mp hu).2⟩
  have h := (Subgroup.mem_inf.mp hu).1
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at h
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
  have ball : ∀ {x : FiniteAdeleRing (𝓞 K) K}, x ∈ idealBall (𝓞 K) K ⊥ → x ∈ idealBall (𝓞 K) K ⊤ :=
    fun hx => rc_mem_idealBall_of_forall_eq_zero K (rc_eq_zero_of_mem_idealBall_bot K hx) ⊤
  exact ⟨⟨⟨h.1.integral, ball h.1.lowerLeft⟩, ball h.1.lowerRight⟩,
    ⟨⟨h.2.integral, ball h.2.lowerLeft⟩, ball h.2.lowerRight⟩⟩

private theorem rc_mem_levelBot_of_mem_levelTop {m : AdelicGL2 (𝓞 K) K}
    (hm : m ∈ levelOne (𝓞 K) K ⊤ ⊓ finiteAdelicGL2Subgroup K)
    (hshape : rc_LowerRowOne K (glFin (𝓞 K) K m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) :
    m ∈ levelOne (𝓞 K) K ⊥ ⊓ finiteAdelicGL2Subgroup K := by
  refine Subgroup.mem_inf.mpr ⟨?_, (Subgroup.mem_inf.mp hm).2⟩
  have htop := (Subgroup.mem_inf.mp hm).1
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at htop
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
  have hinv := rc_lowerRowOne_inv K hshape
  refine ⟨⟨⟨htop.1.integral, ?_⟩, ?_⟩, ⟨⟨htop.2.integral, ?_⟩, ?_⟩⟩
  · exact rc_mem_idealBall_of_forall_eq_zero K (fun w => (hshape w).1) ⊥
  · exact rc_mem_idealBall_of_forall_eq_zero K
      (fun w => by rw [coe_sub_apply, coe_one_apply, (hshape w).2, sub_self]) ⊥
  · exact rc_mem_idealBall_of_forall_eq_zero K (fun w => (hinv w).1) ⊥
  · exact rc_mem_idealBall_of_forall_eq_zero K
      (fun w => by rw [coe_sub_apply, coe_one_apply, (hinv w).2, sub_self]) ⊥

private theorem rc_lowerRowOne_of_mem_doubleCoset_bot {x : AdelicGL2 (𝓞 K) K} (v : HeightOneSpectrum (𝓞 K))
    (hx : x ∈ HeckePair.doubleCoset (levelOne (𝓞 K) K ⊥ ⊓ finiteAdelicGL2Subgroup K) (heckeGen (𝓞 K) K v)) :
    rc_LowerRowOne K (glFin (𝓞 K) K x : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := by
  obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
  exact rc_lowerRowOne_mul K (rc_lowerRowOne_mul K (rc_lowerRowOne_of_mem_levelBot K hu)
    (rc_lowerRowOne_glFin_diagOne K (uniformizerIdele K v))) (rc_lowerRowOne_of_mem_levelBot K hu')

private theorem rc_mem_doubleCoset_top_of_mem_doubleCoset_bot {x : AdelicGL2 (𝓞 K) K} (v : HeightOneSpectrum (𝓞 K))
    (hx : x ∈ HeckePair.doubleCoset (levelOne (𝓞 K) K ⊥ ⊓ finiteAdelicGL2Subgroup K) (heckeGen (𝓞 K) K v)) :
    x ∈ HeckePair.doubleCoset (levelOne (𝓞 K) K ⊤ ⊓ finiteAdelicGL2Subgroup K) (heckeGen (𝓞 K) K v) := by
  obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  exact HeckePair.mem_doubleCoset_iff.mpr
    ⟨u, rc_levelBot_le_levelTop K hu, u', rc_levelBot_le_levelTop K hu', rfl⟩

private theorem rc_lowerRowOne_finEmbed_localEmbed (v : HeightOneSpectrum (𝓞 K))
    (g : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K))
    (h0 : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)
    (h1 : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = 1) :
    rc_LowerRowOne K (glFin (𝓞 K) K (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v g)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) := by
  intro w
  rw [glFin_finEmbed, coe_localEmbed]
  by_cases hw : w = v
  · subst hw
    rw [localMat_apply_self, localMat_apply_self, h0, h1]
    exact ⟨rfl, rfl⟩
  · rw [localMat_apply_of_ne (𝓞 K) K v _ 1 0 hw, localMat_apply_of_ne (𝓞 K) K v _ 1 1 hw]
    exact ⟨by simp, by simp⟩

private theorem rc_lowerRowOne_repSome (v : HeightOneSpectrum (𝓞 K)) (ϖ : v.adicCompletionIntegers K)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0) (b : v.adicCompletionIntegers K) :
    rc_LowerRowOne K (glFin (𝓞 K) K (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v (localRepSome ϖ hϖ0 b))) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :=
  rc_lowerRowOne_finEmbed_localEmbed K v _ (by simp) (by simp)

private theorem rc_not_mk_eq_repInf (v : HeightOneSpectrum (𝓞 K)) (ϖ : v.adicCompletionIntegers K)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hϖ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) {x : AdelicGL2 (𝓞 K) K}
    (hx : rc_LowerRowOne K (glFin (𝓞 K) K x : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)))
    (h : (QuotientGroup.mk x : AdelicGL2 (𝓞 K) K ⧸ (levelOne (𝓞 K) K ⊤ ⊓ finiteAdelicGL2Subgroup K))
      = QuotientGroup.mk (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v (localRepInf ϖ hϖ0)))) : False := by
  classical
  have hm := QuotientGroup.eq.mp h

  set m : AdelicGL2 (𝓞 K) K := x⁻¹ * finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v (localRepInf ϖ hϖ0)) with hm_def
  have hrow : (glFin (𝓞 K) K m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 0 v = 0 ∧
      (glFin (𝓞 K) K m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 1 v
        = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ := by
    rw [hm_def, map_mul, map_inv, Units.val_mul, glFin_finEmbed]
    rw [(rc_lowerRow_mul K (rc_lowerRowOne_inv K hx) _ v).1, (rc_lowerRow_mul K (rc_lowerRowOne_inv K hx) _ v).2]
    rw [coe_localEmbed, localMat_apply_self, localMat_apply_self, coe_localRepInf]
    simp

  have hint := (Subgroup.mem_inf.mp hm).1
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at hint
  have hy : ((glFin (𝓞 K) K m)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 K) K))
      ((1 : Fin 2)) 1 v ∈ v.adicCompletionIntegers K := hint.2.integral 1 1 v
  have hprod : (glFin (𝓞 K) K m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 0 v *
        ((glFin (𝓞 K) K m)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 0 1 v +
      (glFin (𝓞 K) K m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 1 v *
        ((glFin (𝓞 K) K m)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 1 v = 1 := by
    have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K) => M 1 1 v)
      (Units.mul_inv (glFin (𝓞 K) K m))
    simpa only [Matrix.mul_apply, Fin.sum_univ_two, coe_add_apply, coe_mul_apply, Matrix.one_apply_eq,
      coe_one_apply] using h1
  rw [hrow.1, zero_mul, zero_add, hrow.2] at hprod
  have hval := congrArg Valued.v hprod
  rw [map_mul, map_one] at hval
  have hϖ' : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ) := hϖ
  rw [hϖ'] at hval
  have hy1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp hy
  have hle : WithZero.exp (-1 : ℤ) * Valued.v (((glFin (𝓞 K) K m)⁻¹ :
      Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 1 v) ≤ WithZero.exp (-1 : ℤ) :=
    mul_le_of_le_one_right' hy1
  rw [hval] at hle
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)

private theorem rc_levelBot_absurd (v : HeightOneSpectrum (𝓞 K)) (ϕ : AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ)
    (hv : IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K ⊥ ⊓ finiteAdelicGL2Subgroup K)
      (heckeGen (𝓞 K) K v) v ϕ c) : False := by
  classical
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := (Ideal.absNorm_ne_zero_iff v.asIdeal).mp
    (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  haveI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  obtain ⟨reps, hsys, -⟩ := hv
  obtain ⟨ϖ, hϖ0, hϖ, -, sec, -, hsysM⟩ :=
    HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen K v
  have hvtop : ¬ v.asIdeal ∣ (⊤ : Ideal (𝓞 K)) := fun hdvd =>
    v.isPrime.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp hdvd))
  have hsysT := hsysM ⊤ hvtop

  have cover : ∀ i, ∃ cc : 𝓞 K ⧸ v.asIdeal,
      (QuotientGroup.mk (reps i) : AdelicGL2 (𝓞 K) K ⧸ (levelOne (𝓞 K) K ⊥ ⊓ finiteAdelicGL2Subgroup K))
        = QuotientGroup.mk (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v (localRepSome ϖ hϖ0
            (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec cc))))) := by
    intro i
    have hmem := hsys.mem_doubleCoset i
    have hshape := rc_lowerRowOne_of_mem_doubleCoset_bot K v hmem
    obtain ⟨j, hj⟩ := hsysT.covers (reps i) (rc_mem_doubleCoset_top_of_mem_doubleCoset_bot K v hmem)
    cases j with
    | none => exact (rc_not_mk_eq_repInf K v ϖ hϖ0 hϖ hshape hj).elim
    | some cc =>
      refine ⟨cc, QuotientGroup.eq.mpr ?_⟩
      have hm := QuotientGroup.eq.mp hj
      refine rc_mem_levelBot_of_mem_levelTop K hm ?_
      rw [map_mul, map_inv, Units.val_mul]
      exact rc_lowerRowOne_mul K (rc_lowerRowOne_inv K hshape) (rc_lowerRowOne_repSome K v ϖ hϖ0 _)
  choose φ hφ using cover
  have hinj : Function.Injective φ := by
    intro i j hij
    apply hsys.mk_injective
    show (QuotientGroup.mk (reps i) : _ ⧸ _) = QuotientGroup.mk (reps j)
    rw [hφ i, hφ j, hij]
  have hcard := Fintype.card_le_of_injective φ hinj
  rw [Fintype.card_fin, rc_card_residue] at hcard
  omega

end RowCDev

open RowCDev in
theorem solution
    (K : Type) [Field K] [NumberField K] (Pi : HeckeEigensystem K ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : Ideal (𝓞 K))
    (ϕ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous ϕ)
    (hunip : ∀ (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), ϕ (unipotentGL2 x * g) = ϕ g)
    (hborel : ∀ γ ∈ borelSubgroup K, ∀ g : AdelicGL2 (𝓞 K) K, ϕ (globalPoints (𝓞 K) K γ * g) = ϕ g)
    (hlevel : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      ϕ (g * u) = ϕ g)
    (heigen : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (heckeGen (𝓞 K) K v) v ϕ (Pi.a v))
    (hcentralEigen : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
      ϕ (centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) * g)
        = (HeckeEigensystem.cNorm v)⁻¹ * Pi.b v * ϕ g) :
    (∀ g : AdelicGL2 (𝓞 K) K, ϕ g = 0) ∨
      ∃ (S₁ : Finset (HeightOneSpectrum (𝓞 K))) (ψ : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ),
        Continuous ψ ∧ ψ (1, 1) ≠ 0 ∧
        (∀ (γ₁ γ₂ : Kˣ) (t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ),
          ψ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) γ₁ * t₁,
              Units.map (algebraMap K (AdeleRing (𝓞 K) K)) γ₂ * t₂) = ψ (t₁, t₂)) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₁ → ∀ t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ,
          HeckeEigensystem.cNorm v * ψ (uniformizerIdele K v * t₁, t₂) + ψ (t₁, uniformizerIdele K v * t₂)
            = Pi.a v * ψ (t₁, t₂)) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₁ → ∀ t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ,
          ψ (uniformizerIdele K v * t₁, uniformizerIdele K v * t₂)
            = (HeckeEigensystem.cNorm v)⁻¹ * Pi.b v * ψ (t₁, t₂)) := by
  classical
  by_cases h0 : ∀ g : AdelicGL2 (𝓞 K) K, ϕ g = 0
  · exact Or.inl h0
  right
  obtain ⟨g₀, hg₀⟩ := not_forall.mp h0
  by_cases hN : N = ⊥
  · exfalso
    obtain ⟨v, hv⟩ := rc_exists_place_notMem K S
    subst hN
    exact rc_levelBot_absurd K v ϕ (Pi.a v) (heigen v hv)
  set S₁ : Finset (HeightOneSpectrum (𝓞 K)) :=
    S ∪ (rc_finite_dvd K N hN).toFinset ∪ (rc_badSet_finite K g₀).toFinset with hS₁
  refine ⟨S₁, fun t => ϕ (rc_torus K t.1 t.2 * g₀), ?_, ?_, ?_, ?_, ?_⟩
  · exact hcont.comp ((rc_continuous_torus K).mul continuous_const)
  · simpa [rc_torus_one_one] using hg₀
  · intro γ₁ γ₂ t₁ t₂
    exact rc_torus_kinv K ϕ hborel g₀ γ₁ γ₂ t₁ t₂
  · intro v hv t₁ t₂
    have hvS : v ∉ S := fun h => hv (by simp [hS₁, h])
    have hvN : ¬ v.asIdeal ∣ N := fun h => hv (by simp [hS₁, h])
    have hvg : rc_comp K g₀ v ∈ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) := by
      by_contra h
      exact hv (by simp [hS₁, rc_badSet, h])
    exact rc_torus_recA K Pi S N ϕ hunip hlevel heigen g₀ v hvS hvN hvg t₁ t₂
  · intro v hv t₁ t₂
    have hvS : v ∉ S := fun h => hv (by simp [hS₁, h])
    exact rc_torus_recB K Pi S ϕ hcentralEigen g₀ v hvS t₁ t₂

#print axioms solution

end
end S_LanglandsTunnell_Converse_eq_zero_or_exists_continuous_torus_recursion_of_unipotent_invariant
end P2MW
export P2MW.S_LanglandsTunnell_Converse_eq_zero_or_exists_continuous_torus_recursion_of_unipotent_invariant (solution)
