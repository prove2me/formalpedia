-- Prove2me | solution 1 for GlobalTheory.SS.OrdProd.ord_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:22:37.657896+00:00
-- url     : https://prove2.me/submissions/3f007207-e3a3-4285-9b68-8b66e0e54a31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeron
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsEqDivOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsVf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStalkDerivationOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LeOfZpowMulUnitEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VectorFieldOrderAddOfProdStrictHenselian
import Theorems.Thm_GlobalTheory_SS_OrdProd_InSpan_closure
import Theorems.Thm_GlobalTheory_SS_OrdProd_InSpan_quot
import Theorems.Thm_GlobalTheory_SS_OrdProd_det_of_inSpan
import Theorems.Thm_GlobalTheory_SS_OrdProd_inSpan_of_cramer
import Theorems.Thm_GlobalTheory_SS_OrdProd_appLE_cstK
import Theorems.Thm_GlobalTheory_SS_OrdProd_exists_lift
import Theorems.Thm_GlobalTheory_SS_OrdProd_jac_block
import Theorems.Thm_GlobalTheory_SS_OrdProd_isFrame_block
import Theorems.Thm_GlobalTheory_SS_OrdProd_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_OrdProd_prod_j_snd
import Theorems.Thm_GlobalTheory_SS_OrdProd_app_appLE
import Theorems.Thm_GlobalTheory_SS_OrdProd_JacEq_res
import Theorems.Thm_GlobalTheory_SS_Ord_existsUnique_hasOrd
import Theorems.Thm_GlobalTheory_SS_PowCmp_le_of_zpow_mul_unit_eq
import Theorems.Thm_GlobalTheory_SS_exists_eq_div_of_isPullback
import Theorems.Thm_GlobalTheory_SS_prod_irr_and_weakNeron


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.OrdProd
variable {K : Type} [Field K]
namespace GlobalTheory.SS.OrdProd
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (π : R), Irreducible π → ∀ (A A' : Over (Sp K)) (I I' : Type) [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] (D : I → VF A) (D' : I' → VF A'), IsFrame D → IsFrame D' → ∃ D₂ : I ⊕ I' → VF (A ⊗ A'), IsFrame D₂ ∧ ∀ (M : Model R A) (N : Model R A') (m n : ℤ), M.Irr → N.Irr → HasOrd M D π m → HasOrd N D' π n → HasOrd (M.prod N) D₂ π (m + n) := by
  intro R K _ _ _ _ _ hSH π hπ A A' I I' _ _ _ _ D D' hD hD'
  have H : IsPullback (fst A A').left (snd A A').left A.hom A'.hom := IsPullback.of_hasPullback _ _
  choose E₁ a₁ a₂ using fun i => exists_lift (fst A A') (snd A A') H (D i)
  choose E₂ b₁ b₂ using fun i => exists_lift (snd A A') (fst A A') H.flip (D' i)
  have hE : IsFrame (Sum.elim E₁ E₂) := isFrame_block H (E := Sum.elim E₁ E₂) a₁ a₂ b₁ b₂ hD hD'
  refine ⟨Sum.elim E₁ E₂, hE, fun M N m n hM hN oM oN => ?_⟩
  have hQ := (_root_.GlobalTheory.SS.prod_irr_and_weakNeron R K hSH A A').1 M N hM hN
  obtain ⟨hdvr, -, -, hfr⟩ := hSH
  have hπ0 : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero
  obtain ⟨k, oQ, -⟩ := _root_.GlobalTheory.SS.Ord.existsUnique_hasOrd R K π hπ (A ⊗ A') _ _ hE (M.prod N) hQ
  suffices hk : k = m + n from hk ▸ oQ
  obtain ⟨U, t, s, ⟨x, hxU, hx⟩, hs, hj⟩ := oM.2
  obtain ⟨U', t', s', ⟨x', hxU', hx'⟩, hs', hj'⟩ := oN.2
  obtain ⟨W, τ, σ, hW, hσ, hjQ⟩ := oQ.2
  let p' : (M.prod N).Y.left ⟶ M.Y.left := (fst M.Y N.Y).left
  let q' : (M.prod N).Y.left ⟶ N.Y.left := (snd M.Y N.Y).left
  have H' : IsPullback p' q' M.Y.hom N.Y.hom := IsPullback.of_hasPullback _ _
  have ep : (M.prod N).j ≫ p' = (fst A A').left ≫ M.j := prod_j_fst M N
  have eq : (M.prod N).j ≫ q' = (snd A A').left ≫ N.j := prod_j_snd M N
  obtain ⟨z, hz, hzU, hzW⟩ : ((M.prod N).sp ∩ (((p' ⁻¹ᵁ U ⊓ q' ⁻¹ᵁ U' : (M.prod N).Y.left.Opens) : Set _) ∩ W)).Nonempty := by
    refine hQ.2 _ _ (p' ⁻¹ᵁ U ⊓ q' ⁻¹ᵁ U').isOpen W.isOpen ?_ (Set.inter_comm _ _ ▸ hW)
    obtain ⟨z, h1, h2⟩ := Scheme.exists_preimage_of_isPullback H' x x' (Eq.trans hx (Eq.symm hx'))
    refine ⟨z, ?_, ?_, ?_⟩
    · show (p' ≫ M.Y.hom) z = _
      rw [Scheme.Hom.comp_apply, h1]; exact hx
    · show p' z ∈ U
      rw [h1]; exact hxU
    · show q' z ∈ U'
      rw [h2]; exact hxU'
  obtain ⟨V, V', W', h₁, h₂, hV, hV', hW', hzW', hg⟩ :=
    _root_.GlobalTheory.SS.exists_eq_div_of_isPullback _ _ _ _ p' q' _ _ H' z U U' W hzU.1 hzU.2 hzW
  have jM := JacEq.res hj hV
  have jN := JacEq.res hj' hV'
  have jQ := JacEq.res hjQ hW'
  have us := hs.map (M.Y.left.presheaf.map (homOfLE hV).op).hom
  have us' := hs'.map (N.Y.left.presheaf.map (homOfLE hV').op).hom
  have uσ := hσ.map ((M.prod N).Y.left.presheaf.map (homOfLE hW').op).hom
  generalize (M.Y.left.presheaf.map (homOfLE hV).op).hom s = s₁ at jM us
  generalize (N.Y.left.presheaf.map (homOfLE hV').op).hom s' = s₂ at jN us'
  generalize ((M.prod N).Y.left.presheaf.map (homOfLE hW').op).hom σ = σ₁ at jQ uσ
  generalize (fun i => (M.Y.left.presheaf.map (homOfLE hV).op).hom (t i)) = t₁ at jM
  generalize (fun i => (N.Y.left.presheaf.map (homOfLE hV').op).hom (t' i)) = t₂ at jN
  generalize (fun i => ((M.prod N).Y.left.presheaf.map (homOfLE hW').op).hom (τ i)) = τ₁ at jQ
  let T : I ⊕ I' → Γ((M.prod N).Y.left, W') :=
    Sum.elim (fun i => (p'.appLE V W' h₁).hom (t₁ i)) fun i => (q'.appLE V' W' h₂).hom (t₂ i)
  have jT : JacEq (M.prod N) (Sum.elim E₁ E₂) (algebraMap R K π ^ (m + n)) W' T
      ((p'.appLE V W' h₁).hom s₁ * (q'.appLE V' W' h₂).hom s₂) := by
    have b := jac_block (E := Sum.elim E₁ E₂) a₁ a₂ b₁ b₂ _ _ _ (pre_le ep h₁) (pre_le eq h₂)
      (fun i => (M.j.app V).hom (t₁ i)) (fun i => (N.j.app V').hom (t₂ i))
    unfold JacEq at jM jN ⊢
    rw [jM, jN, map_mul, map_mul, appLE_cstK, appLE_cstK, ← app_appLE ep h₁, ← app_appLE eq h₂] at b
    rw [zpow_add₀ hπ0, map_mul, map_mul, _root_.mul_mul_mul_comm, ← b]
    congr 1
    funext i
    rcases i with i | i
    · exact app_appLE ep h₁ _
    · exact app_appLE eq h₂ _
  have uT : IsUnit ((p'.appLE V W' h₁).hom s₁ * (q'.appLE V' W' h₂).hom s₂) := (us.map _).mul (us'.map _)
  have hne : ((W' : Set (M.prod N).Y.left) ∩ (M.prod N).sp).Nonempty := ⟨z, hzW', hz⟩
  apply le_antisymm
  · obtain ⟨ρ, hρ⟩ := oQ.1 W' T
    exact _root_.GlobalTheory.SS.PowCmp.le_of_zpow_mul_unit_eq R K π hπ _ (M.prod N) W' hne _ ρ _ _ uT (jT.symm.trans hρ)
  · have hl : ∀ i a b, ((Sum.elim E₁ E₂ i).D ((M.prod N).j ⁻¹ᵁ W')) (a * b) = _ := fun i a b =>
      (Sum.elim E₁ E₂ i).leibniz _ a b
    have hgen : ∀ u ∈ Set.range (p'.appLE V W' h₁).hom ∪ Set.range (q'.appLE V' W' h₂).hom,
        InSpan ((M.prod N).j.app W').hom (fun i => (Sum.elim E₁ E₂ i).D ((M.prod N).j ⁻¹ᵁ W')) T u := by
      rintro _ (⟨u, rfl⟩ | ⟨u, rfl⟩)
      · obtain ⟨r, hr⟩ := inSpan_of_cramer (φ := (M.j.app V).hom) (d := fun i => (D i).D (M.j ⁻¹ᵁ V))
          (((zpow_ne_zero m hπ0).isUnit).map (cstK A _)) (oM.1 V) us jM u
        refine ⟨Sum.elim (fun l => (p'.appLE V W' h₁).hom (r l)) 0, fun i => ?_⟩
        rw [Fintype.sum_sum_type]
        simp only [T, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero,
          add_zero, app_appLE ep]
        rcases i with i | i
        · simp only [Sum.elim_inl, a₁ i _ _ _ _, hr, map_sum, map_mul]
        · simp only [Sum.elim_inr, b₂ i _ _ _ _]
          simp [VF.zero]
      · obtain ⟨r, hr⟩ := inSpan_of_cramer (φ := (N.j.app V').hom) (d := fun i => (D' i).D (N.j ⁻¹ᵁ V'))
          (((zpow_ne_zero n hπ0).isUnit).map (cstK A' _)) (oN.1 V') us' jN u
        refine ⟨Sum.elim 0 (fun l => (q'.appLE V' W' h₂).hom (r l)), fun i => ?_⟩
        rw [Fintype.sum_sum_type]
        simp only [T, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero,
          zero_add, app_appLE eq]
        rcases i with i | i
        · simp only [Sum.elim_inl, a₂ i _ _ _ _]
          simp [VF.zero]
        · simp only [Sum.elim_inr, b₁ i _ _ _ _, hr, map_sum, map_mul]
    obtain ⟨ρ, hρ⟩ := det_of_inSpan (φ := ((M.prod N).j.app W').hom)
      (d := fun i => (Sum.elim E₁ E₂ i).D ((M.prod N).j ⁻¹ᵁ W')) (T := T) (τ := τ₁) fun j => by
        obtain ⟨a, ha, b, hb, hu, e⟩ := hg (τ₁ j)
        exact InSpan.quot hl (InSpan.closure hl hgen ha) (InSpan.closure hl hgen hb) hu e
    refine _root_.GlobalTheory.SS.PowCmp.le_of_zpow_mul_unit_eq R K π hπ _ (M.prod N) W' hne σ₁
      (ρ * ((p'.appLE V W' h₁).hom s₁ * (q'.appLE V' W' h₂).hom s₂)) _ _ uσ ?_
    refine (Eq.symm jQ).trans (hρ.trans ((congrArg _ jT).trans ?_))
    rw [map_mul _ ρ]; ring
end GlobalTheory.SS.OrdProd
