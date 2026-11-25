-- Prove2me | solution 1 for GlobalTheory.ChF.eigB_res_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:05:10.096832+00:00
-- url     : https://prove2.me/submissions/8c0d9748-06e0-486a-a51a-a2e80ece22c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EigenbasisRestrictionSurjectiveEquivariant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_ne_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
namespace GlobalTheory.ChF
private theorem exists_leftInv {O OE : Type} [CommRing O] [IsDomain O] [ValuationRing O] [CommRing OE] {d n : ℕ}
    (ρ : OE → Matrix (Fin d) (Fin d) O) (τ : OE →+* O) (W : Fin n → Fin d → O) (h : EigB ρ τ W) :
    ∃ G : Matrix (Fin n) (Fin d) O, ∀ i, G *ᵥ W i = Pi.single i 1 := by
  classical
  let φ : (Fin n → O) →ₗ[O] (Fin d → O) := Fintype.linearCombination O W
  have hφ : ∀ c, φ c = ∑ i, c i • W i := fun c => Fintype.linearCombination_apply O W c
  have heig : ∀ c a, (ρ a) *ᵥ φ c = τ a • φ c := by
    intro c a
    rw [hφ, Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, h.1, smul_comm]
  have hinj : Function.Injective φ := by
    intro c c' hc
    obtain ⟨c₀, -, hu⟩ := h.2 (φ c) (heig c)
    rw [hu c (hφ c).symm, hu c' (by rw [hc]; exact (hφ c').symm)]
  have htf : Submodule.torsion O ((Fin d → O) ⧸ LinearMap.range φ) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨t, ht⟩, hx⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
    have hx' : (Submodule.Quotient.mk (t • y) : (Fin d → O) ⧸ LinearMap.range φ) = 0 := by
      rw [Submodule.Quotient.mk_smul]; exact hx
    rw [Submodule.Quotient.mk_eq_zero] at hx'
    obtain ⟨c, hc⟩ := hx'
    have hy : ∀ a, (ρ a) *ᵥ y = τ a • y := by
      intro a
      have := heig c a
      rw [hc, Matrix.mulVec_smul, smul_comm] at this
      exact smul_right_injective _ ht0 this
    obtain ⟨c₀, hc₀, -⟩ := h.2 y hy
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact ⟨c₀, (hφ c₀).trans hc₀⟩
  haveI : Module.Flat O ((Fin d → O) ⧸ LinearMap.range φ) :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr htf
  haveI : Module.Free O ((Fin d → O) ⧸ LinearMap.range φ) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range φ).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have hmem : ∀ y, (LinearMap.id - s ∘ₗ (LinearMap.range φ).mkQ : (Fin d → O) →ₗ[O] (Fin d → O)) y ∈ LinearMap.range φ := by
    intro y
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have := LinearMap.congr_fun hs ((LinearMap.range φ).mkQ y)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub, this, sub_self]
  let g : (Fin d → O) →ₗ[O] (Fin n → O) :=
    (LinearEquiv.ofInjective φ hinj).symm.toLinearMap ∘ₗ LinearMap.codRestrict _ _ hmem
  have hg : ∀ c, g (φ c) = c := by
    intro c
    have h0 : (LinearMap.range φ).mkQ (φ c) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact ⟨c, rfl⟩
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq]
    ext1
    simp only [LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, h0,
      map_zero, sub_zero, LinearEquiv.ofInjective_apply]
  refine ⟨LinearMap.toMatrix' g, fun i => ?_⟩
  rw [LinearMap.toMatrix'_mulVec, ← hg (Pi.single i 1), hφ]
  congr 1
  simp [Pi.single_apply]
end GlobalTheory.ChF
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (OE : Type) [CommRing OE] (d n : ℕ) (ρ : OE → Matrix (Fin d) (Fin d) O) (τ : OE →+* O) (W : Fin n → Fin d → O), EigB ρ τ W → Function.Surjective (Pdiv.ChartF.res W) ∧ (∀ a f, Pdiv.ChartF.res W ((ρ a)ᵀ *ᵥ f) = τ a • Pdiv.ChartF.res W f) ∧ eigDim C ρ ((algebraMap O C).comp τ) = n := by
  classical
  intro C _ v O _ _ hv OE _ d n ρ τ W h
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsFractionRing O C := hv.isFractionRing
  obtain ⟨G, hG⟩ := exists_leftInv ρ τ W h
  refine ⟨fun c => ⟨Gᵀ *ᵥ c, ?_⟩, fun a f => ?_, ?_⟩
  · have h1 : Matrix.of W * Gᵀ = 1 := by
      ext i k
      have := congrFun (hG i) k
      simp only [Matrix.mulVec, dotProduct, Pi.single_apply] at this
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.one_apply, eq_comm (a := i), ← this, mul_comm]
    simp only [Pdiv.ChartF.res, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  · ext i
    have : Pdiv.ChartF.res W ((ρ a)ᵀ *ᵥ f) i = W i ⬝ᵥ ((ρ a)ᵀ *ᵥ f) := rfl
    rw [this, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h.1, smul_dotProduct]
    rfl
  · let W' : Fin n → Fin d → C := fun i => algebraMap O C ∘ W i
    have hmap : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin d) O) (y : Fin d → O),
        M.map (algebraMap O C) *ᵥ (algebraMap O C ∘ y) = algebraMap O C ∘ (M *ᵥ y) := by
      intro m M y
      ext k
      exact (RingHom.map_mulVec (algebraMap O C) M y k).symm
    have hli : LinearIndependent C W' := by
      refine LinearIndependent.of_comp (Matrix.mulVecLin (G.map (algebraMap O C))) ?_
      have : (Matrix.mulVecLin (G.map (algebraMap O C))) ∘ W' = Pi.basisFun C (Fin n) := by
        funext i
        simp only [Function.comp_apply, Matrix.mulVecLin_apply, W', hmap, hG]
        ext k
        simp [Pi.single_apply, apply_ite]
      rw [this]
      exact (Pi.basisFun C (Fin n)).linearIndependent
    have hsp : (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C)))
        (((algebraMap O C).comp τ) a)) = Submodule.span C (Set.range W') := by
      apply le_antisymm
      · intro x hx
        simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hx
        obtain ⟨⟨b, hb⟩, hbx⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) x
        choose y hy using hbx
        have hb0 : algebraMap O C b ≠ 0 := by
          rw [map_ne_zero_iff _ hv.hom_inj]; exact nonZeroDivisors.ne_zero hb
        have hyx : algebraMap O C ∘ y = algebraMap O C b • x := by
          ext k
          simp only [Function.comp_apply, hy k, Pi.smul_apply, Algebra.smul_def]
          rfl
        have hye : ∀ a, (ρ a) *ᵥ y = τ a • y := by
          intro a
          ext k
          apply hv.hom_inj
          have := congrFun (hmap (ρ a) y) k
          rw [hyx, Matrix.mulVec_smul, hx a, smul_comm, ← hyx] at this
          simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, RingHom.comp_apply] at this
          simp only [Pi.smul_apply, smul_eq_mul, map_mul, ← this]
        obtain ⟨c, hc, -⟩ := h.2 y hye
        rw [← Submodule.smul_mem_iff _ hb0, ← hyx, ← hc]
        have : algebraMap O C ∘ (∑ i, c i • W i) = ∑ i, algebraMap O C (c i) • W' i := by
          ext k
          simp [W', Finset.sum_apply, Algebra.smul_def]
        rw [this]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        simp only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
        intro a
        simp only [W', hmap, h.1]
        ext k
        simp
    unfold eigDim
    rw [hsp, finrank_span_eq_card hli, Fintype.card_fin]
end GlobalTheory.ChF
