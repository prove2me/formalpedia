-- Prove2me | solution 1 for GlobalTheory.JR.TorusCutOff.exists_unitary_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:52.97098+00:00
-- url     : https://prove2.me/submissions/50153096-6321-455f-8253-218b4c461c7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLocallyConstantCutoffClosedEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjugatesSeparableMatrixCompactModCentralizerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyEtaleGeneratorMulMatrixSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitaryGroupTorusCutoff
import Theorems.Thm_GlobalTheory_ClassParam_Intw_mul
import Theorems.Thm_GlobalTheory_ClassParam_Iso_mul
import Theorems.Thm_GlobalTheory_CutOff_exists_cutoff
import Theorems.Thm_GlobalTheory_JR_Et_uHom_apply
import Theorems.Thm_GlobalTheory_OrbCpt_orbit_cpt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.JR.TorusCutOff
open Matrix MeasureTheory Filter Topology in
private lemma charpoly_separable_of_isGen {F E : Type} [NontriviallyNormedField F]
    [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [_root_.GlobalTheory.JR.Unram F E] (A : _root_.GlobalTheory.JR.Et F E) (r : ℕ)
    (τ : A.K) (p : Fin r → F) (hτ : A.IsGen τ p)
    (j : A.L ≃ₗ[E] (Fin r → E)) (M : Matrix (Fin r) (Fin r) E)
    (hM : ∀ z, j (algebraMap A.K A.L τ * z) = M *ᵥ j z) :
    M.charpoly.Separable := by
  haveI : Module.Finite E A.L :=
    Module.Finite.equiv (A.push).out.equiv
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [Matrix.charpoly, Matrix.det_isEmpty]
    exact Polynomial.separable_one
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨hli, hfin, -⟩ := hτ
  haveI : CharZero F := _root_.GlobalTheory.JR.Unram.charZero E
  let b : Module.Basis (Fin r) F A.K :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hfin])
  let pb : PowerBasis F A.K := ⟨τ, r, b, fun i => by simp [b]⟩
  have h1 : (LinearMap.mul F A.K τ).charpoly = minpoly F τ := by
    rw [← LinearMap.charpoly_toMatrix _ b]
    exact charpoly_leftMulMatrix pb
  let e := (A.push).out.equiv
  let f : Module.End E A.L :=
    LinearMap.mul E A.L (algebraMap A.K A.L τ)
  have key : ∀ w, e ((LinearMap.mul F A.K τ).baseChange E w) = f (e w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c k => simp [e, f, IsBaseChange.equiv_tmul, mul_smul_comm]
    | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  have h3 : e.conj ((LinearMap.mul F A.K τ).baseChange E) = f := by
    apply LinearMap.ext
    intro y
    rw [LinearEquiv.conj_apply]
    simp [key]
  have h4 : M.charpoly = f.charpoly := by
    have : Matrix.toLin' M = j.conj f := by
      apply LinearMap.ext
      intro v
      obtain ⟨z, rfl⟩ := j.surjective v
      simp [LinearEquiv.conj_apply, f, hM]
    rw [← Matrix.charpoly_toLin', this, LinearEquiv.charpoly_conj]
  rw [h4, ← h3, LinearEquiv.charpoly_conj, LinearMap.charpoly_baseChange, h1]
  refine Polynomial.Separable.map ?_
  rw [PerfectField.separable_iff_squarefree]
  exact (minpoly.isRadical F τ).squarefree (minpoly.ne_zero (Algebra.IsIntegral.isIntegral τ))
open Matrix MeasureTheory Filter Topology in
private lemma map_mul_of_commute_generator {F E : Type} [NontriviallyNormedField F]
    [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    (A : _root_.GlobalTheory.JR.Et F E) (τ : A.K) (hτ : Algebra.adjoin F {τ} = ⊤)
    (φ : A.L →ₗ[E] A.L)
    (hφ : ∀ w, φ (algebraMap A.K A.L τ * w) =
      algebraMap A.K A.L τ * φ w) :
    ∀ y w, φ (y * w) = y * φ w := by
  have hK : ∀ k : A.K, ∀ w, φ (algebraMap A.K A.L k * w) =
      algebraMap A.K A.L k * φ w := by
    intro k
    have hk : k ∈ Algebra.adjoin F {τ} := by rw [hτ]; trivial
    induction hk using Algebra.adjoin_induction with
    | mem k hk => rw [Set.mem_singleton_iff.1 hk]; exact hφ
    | algebraMap c =>
      intro w
      rw [← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, ← Algebra.smul_def,
        ← algebraMap_smul E c w, ← algebraMap_smul E c (φ w), map_smul]
    | add k₁ k₂ _ _ h₁ h₂ => intro w; rw [map_add, add_mul, map_add, h₁, h₂, add_mul]
    | mul k₁ k₂ _ _ h₁ h₂ => intro w; rw [RingHom.map_mul, mul_assoc, h₁, h₂, ← mul_assoc]
  intro y
  obtain ⟨u, rfl⟩ := (A.push).out.equiv.surjective y
  induction u using TensorProduct.induction_on with
  | zero => intro w; simp
  | tmul c k =>
    intro w
    rw [IsBaseChange.equiv_tmul, smul_mul_assoc, map_smul, smul_mul_assoc]
    simp only [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom']
    rw [hK]
  | add u₁ u₂ h₁ h₂ => intro w; rw [map_add, add_mul, map_add, h₁, h₂, add_mul]
open Matrix MeasureTheory Filter Topology in
private lemma adjoin_eq_whole_of_isGen {F E : Type} [NontriviallyNormedField F]
    [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    (A : _root_.GlobalTheory.JR.Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F)
    (hτ : A.IsGen τ p) : Algebra.adjoin F {τ} = ⊤ := by
  obtain ⟨hli, hfin, -⟩ := hτ
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · haveI : Subsingleton A.K := Module.finrank_zero_iff.1 hfin
    refine eq_top_iff.2 fun k _ => ?_
    rw [Subsingleton.elim k 1]
    exact Subalgebra.one_mem _
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  let b : Module.Basis (Fin r) F A.K :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hfin])
  let pb : PowerBasis F A.K := ⟨τ, r, b, fun i => by simp [b]⟩
  exact pb.adjoin_gen_eq_top
open Matrix MeasureTheory Filter Topology in
private lemma exists_uHom_eq_of_mulVec_eq {F E : Type} [NontriviallyNormedField F]
    [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    (A : _root_.GlobalTheory.JR.Et F E) (r : ℕ) (x : A.K)
    (j : A.L ≃ₗ[E] (Fin r → E)) (hx : A.IsIsom x j)
    (t : Matrix.unitaryGroup (Fin r) E) (y : A.L)
    (hy : ∀ z, t.1 *ᵥ j z = j (y * z)) :
    ∃ s, A.uHom hx s = t := by
  have hform : ∀ a b, star (j a) ⬝ᵥ j b = Algebra.trace E A.L
      (algebraMap A.K A.L x * star a * b) := hx
  have hpres : ∀ v w : Fin r → E, star (t.1 *ᵥ v) ⬝ᵥ (t.1 *ᵥ w) = star v ⬝ᵥ w := by
    intro v w
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      ← Matrix.star_eq_conjTranspose, t.2.1, Matrix.vecMul_one]
  have hnd : ∀ w : Fin r → E, (∀ a, star (j a) ⬝ᵥ w = 0) → w = 0 := by
    intro w hw
    funext i
    have := hw (j.symm (Pi.single i 1))
    simpa using this
  have hc : star y * y = 1 := by
    have h0 : ∀ b, (star y * y - 1) * b = 0 := by
      intro b
      apply j.injective
      rw [map_zero]
      apply hnd
      intro a
      have h := hpres (j a) (j b)
      rw [hy, hy, hform, hform] at h
      rw [hform, sub_mul, mul_sub, map_sub, sub_eq_zero, one_mul, ← h, star_mul]
      congr 1
      ring
    simpa [sub_eq_zero] using h0 1
  have hs : y ∈ unitary A.L := ⟨hc, by rw [mul_comm]; exact hc⟩
  refine ⟨⟨y, hs⟩, Subtype.ext ?_⟩
  rw [_root_.GlobalTheory.JR.Et.uHom_apply]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  obtain ⟨z, rfl⟩ := j.surjective v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply,
    _root_.GlobalTheory.JR.Et.mulMat_mulVec_apply, hy]
open Matrix MeasureTheory Filter Topology in
private lemma isClosedEmbedding_uHom {F E : Type} [NontriviallyNormedField F]
    [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [_root_.GlobalTheory.JR.Unram F E] (A : _root_.GlobalTheory.JR.Et F E) (r : ℕ)
    (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E))
    (hx : A.IsIsom x j) [IsTopologicalRing A.L]
    [ContinuousStar A.L] [ContinuousStar E] :
    IsClosedEmbedding (A.uHom hx) := by
  haveI : LocallyCompactSpace F :=
    _root_.GlobalTheory.JR.Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by
    rw [_root_.GlobalTheory.JR.Unram.finrank_eq (F := F) (E := E)]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  have hj : Continuous j :=
    IsModuleTopology.continuous_of_linearMap (R := F) (j.toLinearMap.restrictScalars F)
  have hjs : Continuous j.symm :=
    IsModuleTopology.continuous_of_linearMap (R := F) (j.symm.toLinearMap.restrictScalars F)
  haveI : T2Space A.L :=
    (Homeomorph.mk j.toEquiv hj hjs).isEmbedding.t2Space
  set u := A.uHom hx with hu
  have hu_mulVec : ∀ s v, (u s).1 *ᵥ v = j (s.1 * j.symm v) := by
    intro s v
    rw [hu, _root_.GlobalTheory.JR.Et.uHom_apply,
      _root_.GlobalTheory.JR.Et.mulMat_mulVec]
  let f : Matrix (Fin r) (Fin r) E → A.L := fun m => j.symm (m *ᵥ j 1)
  have hf : Continuous f := hjs.comp (continuous_id.matrix_mulVec continuous_const)
  have hg : Continuous (fun s => (u s).1) := by
    refine continuous_pi fun i => continuous_pi fun k => ?_
    have : (fun s => (u s).1 i k) = fun s => (j (s.1 * j.symm (Pi.single k 1))) i := by
      funext s
      rw [← hu_mulVec]
      simp [Matrix.mulVec_single]
    rw [this]
    exact (continuous_apply i).comp (hj.comp (continuous_subtype_val.mul continuous_const))
  have hfg : ∀ s, f (u s).1 = s.1 := by
    intro s
    simp [f, hu_mulVec]
  have hemb : IsEmbedding (fun s => (u s).1) :=
    IsEmbedding.of_comp hg hf (by
      have : f ∘ (fun s => (u s).1) = Subtype.val := funext hfg
      rw [this]
      exact IsEmbedding.subtypeVal)
  have hrange : Set.range (fun s => (u s).1) =
      {m | f m ∈ unitary A.L} ∩ ⋂ v, {m | m *ᵥ v = j (f m * j.symm v)} := by
    ext m
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨by simp [hfg], Set.mem_iInter.2 fun v => ?_⟩
      simp only [Set.mem_setOf_eq, hfg, hu_mulVec]
    · rintro ⟨h₁, h₂⟩
      refine ⟨⟨f m, h₁⟩, ?_⟩
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hu_mulVec]
      exact (Set.mem_iInter.1 h₂ v).symm
  have hclosed : IsClosed (Set.range (fun s => (u s).1)) := by
    rw [hrange]
    exact (isClosed_unitary.preimage hf).inter (isClosed_iInter fun v =>
      isClosed_eq (continuous_id.matrix_mulVec continuous_const)
        (hj.comp (hf.mul continuous_const)))
  have hval : IsClosedEmbedding
      (Subtype.val : Matrix.unitaryGroup (Fin r) E → Matrix (Fin r) (Fin r) E) :=
    (isClosed_unitary (R := Matrix (Fin r) (Fin r) E)).isClosedEmbedding_subtypeVal
  exact (IsClosedEmbedding.of_comp_iff hval).1 ⟨hemb, hclosed⟩
end GlobalTheory.JR.TorusCutOff
end

set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.TorusCutOff
open Matrix MeasureTheory Filter Topology
namespace GlobalTheory.JR.TorusCutOff
namespace _root_.GlobalTheory.JR.TorusCutOff
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [_root_.GlobalTheory.JR.Unram F E] (A : _root_.GlobalTheory.JR.Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F), A.IsGen τ p → ∀ (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (hx : A.IsIsom x j) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) → ∀ (ν : Measure (unitary A.L)), ν.IsHaarMeasure → ∀ Z : Set (Matrix (Fin r) (Fin r) E), IsCompact Z → ∃ α : Matrix.unitaryGroup (Fin r) E → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ g : Matrix.unitaryGroup (Fin r) E, g.1 * Ax.1 * star g.1 ∈ Z → ∫ t, α (g * (A.uHom hx t)⁻¹) ∂ν = 1 := by
  intro F E _ _ _ _ _ A r τ p hτ x j hx Ax hAx ν _ Z hZ
  haveI : LocallyCompactSpace E :=
    _root_.GlobalTheory.JR.Unram.lcE F
  haveI : IsUltrametricDist E := _root_.GlobalTheory.JR.Unram.ultraE F
  haveI : ContinuousStar E := ⟨(AddMonoidHomClass.isometry_of_norm (starAddEquiv : E ≃+ E)
    (_root_.GlobalTheory.JR.Unram.norm_star F)).continuous⟩
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by
    rw [_root_.GlobalTheory.JR.Unram.finrank_eq (F := F) (E := E)]; norm_num)
  haveI : Module.Finite E A.L :=
    Module.Finite.equiv (A.push).out.equiv
  haveI : Module.Finite F A.L := Module.Finite.trans E _
  haveI : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F _
  haveI : ContinuousStar A.L := by
    refine ⟨?_⟩
    let σ : A.L →ₗ[F] A.L :=
      { toFun := star
        map_add' := star_add
        map_smul' := fun a y => by
          rw [Algebra.smul_def, star_mul, IsScalarTower.algebraMap_apply F E A.L,
            A.star_E,
            _root_.GlobalTheory.JR.Unram.star_fix,
            ← IsScalarTower.algebraMap_apply, ← Algebra.commutes, ← Algebra.smul_def]
          rfl }
    exact IsModuleTopology.continuous_of_linearMap (R := F) σ
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) E) :=
    (inferInstance : LocallyCompactSpace (Fin r → Fin r → E))
  haveI : TotallyDisconnectedSpace (Matrix (Fin r) (Fin r) E) :=
    (inferInstance : TotallyDisconnectedSpace (Fin r → Fin r → E))
  haveI : LocallyCompactSpace (Matrix.unitaryGroup (Fin r) E) :=
    (isClosed_unitary (R := Matrix (Fin r) (Fin r) E)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hsep : Ax.1.charpoly.Separable :=
    charpoly_separable_of_isGen A r τ p hτ j Ax.1 hAx
  have hcent : ∀ t : Matrix.unitaryGroup (Fin r) E, t.1 * Ax.1 = Ax.1 * t.1 →
      ∃ s, A.uHom hx s = t := by
    intro t ht
    let φ : A.L →ₗ[E] A.L :=
      j.symm.toLinearMap ∘ₗ Matrix.toLin' t.1 ∘ₗ j.toLinearMap
    have hφ : ∀ w, φ (algebraMap A.K A.L τ * w) =
        algebraMap A.K A.L τ * φ w := by
      intro w
      apply j.injective
      simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.toLin'_apply,
        LinearEquiv.apply_symm_apply]
      rw [hAx, hAx, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, ht,
        ← Matrix.mulVec_mulVec]
    have hmul := map_mul_of_commute_generator A τ
      (adjoin_eq_whole_of_isGen A r τ p hτ) φ hφ
    refine exists_uHom_eq_of_mulVec_eq A r x j hx t (φ 1) (fun z => ?_)
    have h1 : j (φ z) = t.1 *ᵥ j z := by simp [φ]
    rw [← h1, mul_comm, ← hmul, mul_one]
  have hemb : IsClosedEmbedding (A.uHom hx) :=
    isClosedEmbedding_uHom A r x j hx
  obtain ⟨C, hC, hCg⟩ :=
    (_root_.GlobalTheory.OrbCpt.orbit_cpt F E r).2 Ax.1 Ax.2 hsep Z hZ
  let i : unitary A.L →* Matrix.unitaryGroup (Fin r) E :=
    (A.uHom hx).comp invMonoidHom
  have hi : IsClosedEmbedding i := hemb.comp (Homeomorph.inv _).isClosedEmbedding
  obtain ⟨α, h₁, h₂, h₃, h₄⟩ := _root_.GlobalTheory.CutOff.exists_cutoff
    (Matrix.unitaryGroup (Fin r) E) (unitary A.L) i hi ν C hC
  refine ⟨α, h₁, h₂, h₃, fun g hg => ?_⟩
  obtain ⟨c, hc, t, ht, rfl⟩ := hCg g hg
  obtain ⟨s, rfl⟩ := hcent t ht
  have := h₄ c hc s⁻¹
  simpa [i, mul_assoc] using this
end _root_.GlobalTheory.JR.TorusCutOff
end GlobalTheory.JR.TorusCutOff
