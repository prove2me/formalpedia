-- Prove2me | solution 1 for HtGaussGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:00:26.355871+00:00
-- url     : https://prove2.me/submissions/47ea4bac-2487-4206-ab60-109b4e9140cf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_TranslSEquivApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericTheorem_HtGaussGen
import Theorems.Thm_BlockPoly_cb_ne_zero
import Theorems.Thm_BlockPoly_multiHom_of_dvd
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_cS_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_comap_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_lift_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_lift_swap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_lift_transl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open NumberField
open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.GaussGen BlockPoly
theorem _root_.solution {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {Ω : ι → Type}
    [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] {WT : Type} [AddCommGroup WT] {A : ι → Type}
    [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
    [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c))
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data K ι Ω WT A)
    (hx1 : ReciprocityTheory.ChartRestriction.G.T0.LeafSt.PlaceTrivialOrPositive 𝒜 d)
    (hx2 : ReciprocityTheory.ChartRestriction.G.T0.LeafSt.AdmissibleValuationPrimeUnique 𝒜 d) :
    ReciprocityTheory.ChartRestriction.G.T0.LeafSt.GeneratorMultiHomogeneous 𝒜 d := by
  unfold ReciprocityTheory.ChartRestriction.G.T0.LeafSt.GeneratorMultiHomogeneous
  intro hd h c p hp hgood
  obtain ⟨w, hw⟩ := hgood
  by_cases hpp : p.IsPrincipal
  swap
  · have h0 : d.gen p = 0 := by
      unfold ReciprocityTheory.ChartRestriction.G.T0.Data.gen
      rw [dif_neg hpp]
    rw [h0]
    unfold ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous
    intro s hs
    simp at hs
  have hgen : d.gen p = Submodule.IsPrincipal.generator p := by
    unfold ReciprocityTheory.ChartRestriction.G.T0.Data.gen
    rw [dif_pos hpp]

  have key : ∀ σ : KTp K d.D d.N ≃ₐ[K] KTp K d.D d.N, p.comap σ = p →
      Submodule.IsPrincipal.generator p ∣ σ (Submodule.IsPrincipal.generator p) := by
    intro σ hσ
    have h1 : Submodule.IsPrincipal.generator p ∈ p.comap σ := by
      rw [hσ]
      exact Submodule.IsPrincipal.generator_mem p
    obtain ⟨r, hr⟩ :=
      (Submodule.IsPrincipal.mem_iff_eq_smul_generator p).mp (Ideal.mem_comap.mp h1)
    exact ⟨r, by rw [hr, smul_eq_mul, mul_comm]⟩
  have h2K : (2 : K) ≠ 0 := two_ne_zero
  have h2 : (2 : Ω c) ≠ 0 := by
    intro h0
    apply h2K
    apply (algebraMap K (Ω c)).injective
    rw [map_ofNat, map_zero]
    exact h0

  have hsc : ∀ b, Submodule.IsPrincipal.generator p ∣
      BlockPoly.diag (BlockPoly.cb b (2 : K)) (Submodule.IsPrincipal.generator p) := by
    intro b
    exact key (BlockPoly.diagEquiv (BlockPoly.cb_ne_zero h2K b))
      (ReciprocityTheory.ChartRestriction.G.T0.GaussGen.comap_eq 𝒜 d hx1 hx2 hd h c p hp w hw _
        (BlockPoly.diagEquiv (ReciprocityTheory.ChartRestriction.G.T0.GaussGen.cS_ne_zero h2 b))
        (fun t => ReciprocityTheory.ChartRestriction.G.T0.GaussGen.lift_scale (d.jc c) (d.x c) b t))
  have hsw : ∀ e : Equiv.Perm (Fin (d.D + 1)), e 0 = 0 → Submodule.IsPrincipal.generator p ∣
      MvPolynomial.rename (BlockPoly.eT e) (Submodule.IsPrincipal.generator p) := by
    intro e he
    exact key (MvPolynomial.renameEquiv K (BlockPoly.eT e))
      (ReciprocityTheory.ChartRestriction.G.T0.GaussGen.comap_eq 𝒜 d hx1 hx2 hd h c p hp w hw _
        (MvPolynomial.renameEquiv (Ω c) (ReciprocityTheory.ChartRestriction.G.T0.GaussGen.eS e))
        (fun t => ReciprocityTheory.ChartRestriction.G.T0.GaussGen.lift_swap (d.jc c) (d.x c) e he t))
  have htr : ∀ a : Fin (d.N + 1) → K, Submodule.IsPrincipal.generator p ∣
      BlockPoly.transl a (Submodule.IsPrincipal.generator p) := by
    intro a
    exact key (BlockPoly.translEquiv a)
      (ReciprocityTheory.ChartRestriction.G.T0.GaussGen.comap_eq 𝒜 d hx1 hx2 hd h c p hp w hw _
        (ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv (d.jc c) (fun j => algebraMap K (Ω c) (a j)))
        (fun t => ReciprocityTheory.ChartRestriction.G.T0.GaussGen.lift_transl (d.jc c) (d.x c) a t))
  rw [hgen]
  unfold ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous
  intro s hs b
  exact BlockPoly.multiHom_of_dvd hsc hsw htr s hs b
