-- Prove2me | solution 1 for GlobalTheory.EigenDer.dof_eq_of_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:35.839808+00:00
-- url     : https://prove2.me/submissions/8649540d-677e-4006-b0ff-272c3904e690

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HasSubstAddSqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsNilpotentOfMemKerJetTruncR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SubstMapAlgebraMap
import Theorems.Thm_GlobalTheory_EigenDer_exists_jet_factor
import Theorems.Thm_GlobalTheory_EigenDer_exists_trunc_one
import Theorems.Thm_GlobalTheory_EigenDer_inr_nilpotent
import Theorems.Thm_GlobalTheory_EigenDer_hasSubst_tanPair
import Theorems.Thm_GlobalTheory_EigenDer_subst_tanPair_fst
import Theorems.Thm_GlobalTheory_EigenDer_subst_tanPair_add
import Theorems.Thm_GlobalTheory_JetSer_eq_of_toJet_eq
import Theorems.Thm_GlobalTheory_JetSer_fnVal_specMap
import Theorems.Thm_GlobalTheory_JetSer_toJetHom_apply
import Theorems.Thm_GlobalTheory_JetSer_toJet_X
import Theorems.Thm_GlobalTheory_JetSer_top_le_preimage_comp
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_zR_mem_ker
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.EigenDer
variable {R : Type} [CommRing R]
namespace GlobalTheory.EigenDer
theorem _root_.solution : JetAlgSt → RepSt → SerSt → ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (d : ℕ) (x : Fam G (Fin d)), IsUnivChart G d x → ∀ Gl : FGLaw R d, IsLawOf x Gl.F → ∀ (U : G.left.Opens), ⊤ ≤ η[G].left ⁻¹ᵁ U → ∀ (s : Γ(G.left, U)) (f : PS R 1 d), IsSer1 x U s f → ∀ (v : Fin d → R) (y : R) (φ : JetR R (Fin d) 1 →ₐ[R] DualNumber R), (∀ i, φ (zR 1 i) = TrivSqZeroExt.inr (v i)) → (∀ (A : Type) [CommRing A] [Algebra R A] (c : DualNumber R →ₐ[R] A) (r : sp (R₀ := R) A ⟶ G), ⊤ ≤ r.left ⁻¹ᵁ U → ⊤ ≤ (r * (spMap c ≫ spMap φ ≫ x 1)).left ⁻¹ᵁ U → fnVal (r * (spMap c ≫ spMap φ ≫ x 1)).left U s = c (1 + TrivSqZeroExt.inr y) * fnVal r.left U s) → Dof Gl.F v f = C y * f := by
  intro _ hRep _ R _ G _ d x hx Gl hl U _ s f hf v y φ hφ H
  have hb := hasSubst_tanPair d v
  have hpt : ∀ (k : Fin 2) (j : Fin d), constantCoeff (pt R (n := 2) d k j) = 0 := fun k j => by
    simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  obtain ⟨y₁, hy₁, -⟩ := (hRep R G d x hx (Fin 2 × Fin d)).1 (pt R d 0) (hpt 0)
  obtain ⟨y₂, hy₂, -⟩ := (hRep R G d x hx (Fin 2 × Fin d)).1 (pt R d 1) (hpt 1)
  have s₁ := hf 2 _ _ hy₁
  have s₁₂ := hf 2 _ _ (hl.2 2 _ _ _ _ hy₁ hy₂)
  have key : subst (tanPair d v) (ev (n := 2) ![addOf Gl.F (pt R d 0) (pt R d 1)] f) =
      C (1 + TrivSqZeroExt.inr y : DualNumber R) * subst (tanPair d v) (ev (n := 2) ![pt R d 0] f) := by
    refine eq_of_toJet_eq fun m => ?_
    let T : PS R 2 d →ₐ[R] JetR (DualNumber R) (Fin 1 × Fin d) m :=
      ((toJetHom (DualNumber R) (Fin 1 × Fin d) m).restrictScalars R).comp (substAlgHom hb)
    have hT : ∀ g, T g = toJet m (subst (tanPair d v) g) := fun g => by
      rw [← substAlgHom_apply hb]; rfl
    let c : DualNumber R →ₐ[R] JetR (DualNumber R) (Fin 1 × Fin d) m := IsScalarTower.toAlgHom R _ _
    have hc : ∀ a, toJet m (C a : PS (DualNumber R) 1 d) = c a := fun a =>
      (toJetHom (DualNumber R) (Fin 1 × Fin d) m).commutes a
    have hT1 : ∀ i, T (X ((1 : Fin 2), i)) = c (TrivSqZeroExt.inr (v i)) := fun i => by
      rw [hT, subst_X hb, ← hc]; rfl
    have hT0 : ∀ i, T (X ((0 : Fin 2), i)) = zR m ((0 : Fin 1), i) := fun i => by
      rw [hT, subst_X hb, ← toJet_X]; rfl
    obtain ⟨n, Θ, hΘ⟩ := exists_jet_factor T (by
      rintro ⟨j, i⟩
      fin_cases j
      · refine hT0 i ▸ ⟨m + 1, ?_⟩
        have := Ideal.pow_mem_pow (zR_mem_ker (R := DualNumber R) m ((0 : Fin 1), i)) (m + 1)
        rwa [ker_jetAug_pow, Ideal.mem_bot] at this
      · exact hT1 i ▸ (inr_nilpotent (v i)).map c)
    obtain ⟨t, ht, htx⟩ := exists_trunc_one x hx.1 n
    obtain ⟨ψ, hψ, hψy⟩ := hy₂.2 (n + 1)
    have e₂ : spMap c ≫ spMap φ ≫ x 1 = spMap Θ ≫ y₂ (n + 1) := by
      have : c.comp (φ.comp t) = Θ.comp ψ := jet_ext fun j => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, ht, hφ, hψ, hΘ]
        exact (hT1 j).symm
      rw [hψy, ← htx, ← Category.assoc (spMap φ), spMap_comp, ← Category.assoc, spMap_comp, this,
        ← Category.assoc, spMap_comp]
    have e : (spMap Θ ≫ y₁ (n + 1)) * (spMap c ≫ spMap φ ≫ x 1) = spMap Θ ≫ (y₁ (n + 1) * y₂ (n + 1)) := by
      rw [e₂, MonObj.comp_mul]
    have h := H _ c (spMap Θ ≫ y₁ (n + 1)) (top_le_preimage_comp _ _ U (s₁ (n + 1)).1)
      (by rw [e]; exact top_le_preimage_comp _ _ U (s₁₂ (n + 1)).1)
    have v₁ := fnVal_specMap Θ.toRingHom _ U (s₁ (n + 1)).1 s
    have v₁₂ := fnVal_specMap Θ.toRingHom _ U (s₁₂ (n + 1)).1 s
    rw [(s₁ (n + 1)).2] at v₁
    rw [(s₁₂ (n + 1)).2] at v₁₂
    rw [e] at h
    have h' := v₁₂.symm.trans (h.trans (congrArg (c (1 + TrivSqZeroExt.inr y) * ·) v₁))
    rw [← toJetHom_apply m (C _ * _), map_mul, toJetHom_apply, toJetHom_apply, hc, ← hT, ← hT, ← hΘ, ← hΘ]
    exact h'
  rw [subst_tanPair_add, subst_tanPair_fst] at key
  ext e
  have := congrArg (fun g => TrivSqZeroExt.snd (coeff e g)) key
  simp only [map_add (coeff e), coeff_C_mul, coeff_map] at this
  simpa [TrivSqZeroExt.algebraMap_eq_inl] using this
end GlobalTheory.EigenDer
