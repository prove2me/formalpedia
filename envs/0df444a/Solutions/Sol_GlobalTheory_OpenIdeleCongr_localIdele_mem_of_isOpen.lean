-- Prove2me | solution 1 for GlobalTheory.OpenIdeleCongr.localIdele_mem_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:58:52.356323+00:00
-- url     : https://prove2.me/submissions/20ff7aa4-a20f-484c-a06e-a11c7376a6f3

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsOpenIdeleSubgroupContainsCongruenceUnits
import Theorems.Thm_GlobalTheory_OpenIdeleCongr_finiteSingle_mem_of_nhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
open GlobalTheory GlobalTheory.OpenIdeleCongr
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.OpenIdeleCongr
theorem _root_.solution (V : Subgroup (Ideles F)) (hV : IsOpen (V : Set (Ideles F))) :
    ∃ (S : Set (HeightOneSpectrum (𝓞 F))) (M : ℕ), S.Finite ∧ ∀ v (x : (v.adicCompletion F)ˣ),
      Valued.v (x : v.adicCompletion F) = 1 →
      (v ∈ S → Valued.v ((x : v.adicCompletion F) - 1) ≤ WithZero.exp (-(M : ℤ))) → localIdele F v x ∈ V := by
  obtain ⟨W, hWo, hWU⟩ := Units.isInducing_embedProduct.isOpen_iff.mp hV
  have hW1 : Units.embedProduct _ (1 : Ideles F) ∈ W := by
    rw [← Set.mem_preimage, hWU]
    exact V.one_mem
  rw [map_one] at hW1
  obtain ⟨W1, hW1n, W2, hW2n, hprod⟩ := mem_nhds_prod_iff.mp (hWo.mem_nhds hW1)
  have hW2' : MulOpposite.op ⁻¹' W2 ∈ nhds (1 : AdeleRing (𝓞 F) F) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hW2n
  have hN : W1 ∩ MulOpposite.op ⁻¹' W2 ∈ nhds ((1 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) :=
    Filter.inter_mem hW1n hW2'
  obtain ⟨Vi, hVi, Vf, hVf, hVprod⟩ := mem_nhds_prod_iff.mp hN
  obtain ⟨S, M, hS, hSV⟩ := finiteSingle_mem_of_nhds Vf hVf
  refine ⟨S, M, hS, fun v x hx hxS => ?_⟩
  have hin : ∀ y : (v.adicCompletion F)ˣ, Valued.v (y : v.adicCompletion F) = 1 →
      (v ∈ S → Valued.v ((y : v.adicCompletion F) - 1) ≤ WithZero.exp (-(M : ℤ))) →
      ((localIdele F v y : Ideles F) : AdeleRing (𝓞 F) F) ∈ W1 ∩ MulOpposite.op ⁻¹' W2 := fun y hy hyS =>
    hVprod ⟨mem_of_mem_nhds hVi, hSV v _ (by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hy.le) hyS⟩
  have hxi : Valued.v ((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  have hxiS : v ∈ S → Valued.v (((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) ≤
      WithZero.exp (-(M : ℤ)) := by
    intro hv
    have e : ((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1 =
        ((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * -((x : v.adicCompletion F) - 1) := by
      rw [mul_neg, mul_sub, Units.inv_mul, mul_one]; ring
    rw [e, map_mul, Valuation.map_neg, hxi, one_mul]
    exact hxS hv
  have h1 := hin x hx hxS
  have h2 := hin x⁻¹ hxi hxiS
  rw [← SetLike.mem_coe, ← hWU, Set.mem_preimage, Units.embedProduct_apply]
  refine hprod ⟨h1.1, ?_⟩
  have h3 := h2.2
  rw [map_inv] at h3
  exact h3
end GlobalTheory.OpenIdeleCongr
