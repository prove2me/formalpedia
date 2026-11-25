-- Prove2me | solution 1 for GlobalTheory.LocFlat.contrFactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:43:59.264363+00:00
-- url     : https://prove2.me/submissions/dc8ca8d6-8ccf-42fc-ac6b-e61fc23a9c9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLinearOfBilinearSchwartzBruhatProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SpanSchwartzBruhatProductEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeisenbergInvariantFactorsContraction
import Theorems.Thm_GlobalTheory_LocFlat_CFac_coe_psi_mul_neg
import Theorems.Thm_GlobalTheory_LocFlat_CFac_coe_psi_add
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_LocFlat_CFac_mulLC_apply
import Theorems.Thm_GlobalTheory_RootEx_OpenKernel_isLocallyConstant_coe_addChar
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_subset
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
import Theorems.Thm_GlobalTheory_SplitWeil_neg_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_StepData_IntM_neg
import Theorems.Thm_GlobalTheory_StepData_MaxM_neg
import Theorems.Thm_GlobalTheory_T_exists_linear_of_bilinear_schwartzBruhatProduct
import Theorems.Thm_GlobalTheory_T_span_schwartzBruhatProduct_eq_top
import Theorems.Thm_GlobalTheory_T_translationInvariant_schwartzBruhat_map_factors_integral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.LocFlat.CFac.mulLC_apply



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.LocFlat
open GlobalTheory.LocFlat.CFac
namespace GlobalTheory.LocFlat
theorem _root_.solution : ContrFactor := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν n n' n'' _ _ _ _ _ _ M _ _ B h1 h2
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI hTD : ∀ (a b : Type) [Fintype a] [Fintype b], TotallyDisconnectedSpace (Matrix a b k) :=
    fun a b _ _ => inferInstanceAs (TotallyDisconnectedSpace (a → b → k))
  haveI hLC : ∀ (a b : Type) [Fintype a] [Fintype b], LocallyCompactSpace (Matrix a b k) :=
    fun a b _ _ => inferInstanceAs (LocallyCompactSpace (a → b → k))
  have hψlc := GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψ hψc
  obtain ⟨l, hl⟩ := GlobalTheory.T.exists_linear_of_bilinear_schwartzBruhatProduct _ _ M B

  set X₁ := Matrix n (n' ⊕ Unit) k
  set X₂ := Matrix (n'' ⊕ Unit) n k

  let uy : X₁ × X₂ → k := fun z => z.2 (Sum.inr ()) ⬝ᵥ fun r => z.1 r (Sum.inr ())
  have huy : Continuous uy := by
    refine Continuous.dotProduct ?_ ?_
    · exact continuous_pi fun r => (continuous_apply r).comp ((continuous_apply (Sum.inr ())).comp continuous_snd)
    · exact continuous_pi fun r => (continuous_apply (Sum.inr ())).comp ((continuous_apply r).comp continuous_fst)
  have hχ : IsLocallyConstant fun z => (ψ (-uy z) : ℂ) := hψlc.comp_continuous huy.neg
  have hχi : IsLocallyConstant fun z => (ψ (uy z) : ℂ) := hψlc.comp_continuous huy
  let L : SB (X₁ × X₂) →ₗ[ℂ] M := l ∘ₗ mulLC _ hχi
  have key : ∀ f g, L (mulLC _ hχ (prodSB f g)) = B f g := by
    intro f g
    rw [← hl]
    show l _ = l _
    congr 1
    ext z
    simp only [mulLC_apply, ← mul_assoc, coe_psi_mul_neg, one_mul]
  have hspan : Submodule.span ℂ (Set.range fun q : SB X₁ × SB X₂ => mulLC _ hχ (prodSB q.1 q.2)) = ⊤ := by
    have hsurj : Function.Surjective (mulLC _ hχ) := fun F => ⟨mulLC _ hχi F, by
      ext z; simp only [mulLC_apply, ← mul_assoc]; rw [mul_comm (ψ (-uy z) : ℂ), coe_psi_mul_neg, one_mul]⟩
    rw [Set.range_comp' (mulLC _ hχ) (fun q : SB X₁ × SB X₂ => prodSB q.1 q.2), Submodule.span_image,
      GlobalTheory.T.span_schwartzBruhatProduct_eq_top, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]

  have transY : ∀ y₀ : n → k, L ∘ₗ comapH (Homeomorph.addRight ((fromCols 0 (Matrix.of fun r _ => y₀ r) : X₁), (0 : X₂))) = L := by
    intro y₀
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨⟨f, g⟩, rfl⟩
    have hc : IsLocallyConstant fun x : X₂ => (ψ (-(x (Sum.inr ()) ⬝ᵥ y₀)) : ℂ) :=
      hψlc.comp_continuous (Continuous.neg (Continuous.dotProduct
        (continuous_pi fun r => (continuous_apply r).comp (continuous_apply (Sum.inr ()))) continuous_const))
    set C : X₁ := fromCols 0 (Matrix.of fun r _ => y₀ r)
    let f' := comapH (Homeomorph.addRight C) f
    let g' := mulLC _ hc g
    have hu : ∀ z : X₁ × X₂, uy (z + (C, 0)) = uy z + z.2 (Sum.inr ()) ⬝ᵥ y₀ := by
      intro z
      simp only [uy, Prod.fst_add, Prod.snd_add, add_zero, Matrix.add_apply, C, fromCols_apply_inr, Matrix.of_apply]
      rw [← dotProduct_add]; rfl
    have e1 : comapH (Homeomorph.addRight (C, (0 : X₂))) (mulLC _ hχ (prodSB f g)) = mulLC _ hχ (prodSB f' g') := by
      ext z
      simp only [comapH_apply, mulLC_apply, prodSB_apply, Homeomorph.coe_addRight, f', g']
      rw [hu, neg_add, coe_psi_add]
      simp only [Prod.fst_add, Prod.snd_add, add_zero]
      ring
    rw [LinearMap.comp_apply, e1, key, key]
    exact h2 y₀ f f' g g' (fun x => rfl) (fun x => rfl)
  have transU : ∀ u₀ : n → k, L ∘ₗ comapH (Homeomorph.addRight ((0 : X₁), (fromRows 0 (Matrix.of fun _ => u₀) : X₂))) = L := by
    intro u₀
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨⟨f, g⟩, rfl⟩
    have hc : IsLocallyConstant fun x : X₁ => (ψ (-(u₀ ⬝ᵥ fun r => x r (Sum.inr ()))) : ℂ) :=
      hψlc.comp_continuous (Continuous.neg (Continuous.dotProduct continuous_const
        (continuous_pi fun r => (continuous_apply (Sum.inr ())).comp (continuous_apply r))))
    set R : X₂ := fromRows 0 (Matrix.of fun _ => u₀)
    let f' := mulLC _ hc f
    let g' := comapH (Homeomorph.addRight R) g
    have hu : ∀ z : X₁ × X₂, uy (z + (0, R)) = uy z + u₀ ⬝ᵥ fun r => z.1 r (Sum.inr ()) := by
      intro z
      simp only [uy, Prod.fst_add, Prod.snd_add, add_zero, Matrix.add_apply, R, fromRows_apply_inr, Matrix.of_apply]
      rw [← add_dotProduct]; rfl
    have e1 : comapH (Homeomorph.addRight ((0 : X₁), R)) (mulLC _ hχ (prodSB f g)) = mulLC _ hχ (prodSB f' g') := by
      ext z
      simp only [comapH_apply, mulLC_apply, prodSB_apply, Homeomorph.coe_addRight, f', g']
      rw [hu, neg_add, coe_psi_add]
      simp only [Prod.fst_add, Prod.snd_add, add_zero]
      ring
    rw [LinearMap.comp_apply, e1, key, key]
    exact h1 u₀ f f' g g' (fun x => rfl) (fun x => rfl)

  set X₀ := Matrix n n' k × Matrix n'' n k
  have hc1 : Continuous fun z : X₁ × X₂ => ((z.1.toCols₁, z.2.toRows₁), ((fun r => z.2 (Sum.inr ()) r), (fun r => z.1 r (Sum.inr ())))) := by
    refine Continuous.prodMk (Continuous.prodMk ?_ ?_) (Continuous.prodMk ?_ ?_)
    · exact continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp ((continuous_apply i).comp continuous_fst)
    · exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply (Sum.inl i)).comp continuous_snd)
    · exact continuous_pi fun r => (continuous_apply r).comp ((continuous_apply (Sum.inr ())).comp continuous_snd)
    · exact continuous_pi fun r => (continuous_apply (Sum.inr ())).comp ((continuous_apply r).comp continuous_fst)
  have hc2 : Continuous fun w : X₀ × ((n → k) × (n → k)) =>
      ((fromCols w.1.1 (Matrix.of fun r _ => w.2.2 r) : X₁), (fromRows w.1.2 (Matrix.of fun _ => w.2.1) : X₂)) := by
    refine Continuous.prodMk ?_ ?_
    · refine continuous_pi fun i => continuous_pi fun j => ?_
      rcases j with j | j
      · exact (continuous_apply j).comp ((continuous_apply i).comp (continuous_fst.comp continuous_fst))
      · exact (continuous_apply i).comp (continuous_snd.comp continuous_snd)
    · refine continuous_pi fun i => continuous_pi fun j => ?_
      rcases i with i | i
      · exact (continuous_apply j).comp ((continuous_apply i).comp (continuous_snd.comp continuous_fst))
      · exact (continuous_apply j).comp (continuous_fst.comp continuous_snd)
  let e : X₁ × X₂ ≃ₜ X₀ × ((n → k) × (n → k)) :=
    { toFun := fun z => ((z.1.toCols₁, z.2.toRows₁), ((fun r => z.2 (Sum.inr ()) r), (fun r => z.1 r (Sum.inr ()))))
      invFun := fun w => (fromCols w.1.1 (Matrix.of fun r _ => w.2.2 r), fromRows w.1.2 (Matrix.of fun _ => w.2.1))
      left_inv := by
        rintro ⟨x₁, x₂⟩
        refine Prod.ext ?_ ?_
        · ext i j; rcases j with j | j <;> rfl
        · ext i j; rcases i with i | i <;> rfl
      right_inv := by
        rintro ⟨⟨p₁, p₂⟩, ⟨u, y⟩⟩
        rfl
      continuous_toFun := hc1
      continuous_invFun := hc2 }

  let L' : SB (X₀ × ((n → k) × (n → k))) →ₗ[ℂ] M := L ∘ₗ comapH e
  have hL' : ∀ (a : (n → k) × (n → k)) (G G' : SB (X₀ × ((n → k) × (n → k)))),
      (∀ z, G'.1 z = G.1 (z.1, z.2 + a)) → L' G' = L' G := by
    rintro ⟨u₀, y₀⟩ G G' hG
    have h3 : comapH e G' = comapH (Homeomorph.addRight ((fromCols 0 (Matrix.of fun r _ => y₀ r) : X₁), (0 : X₂)))
        (comapH (Homeomorph.addRight ((0 : X₁), (fromRows 0 (Matrix.of fun _ => u₀) : X₂))) (comapH e G)) := by
      ext z
      simp only [comapH_apply, Homeomorph.coe_addRight]
      rw [hG]
      refine congrArg G.1 ?_
      refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
      · ext i j; show z.1 i (Sum.inl j) = z.1 i (Sum.inl j) + 0 + 0; simp
      · ext i j; show z.2 (Sum.inl i) j = z.2 (Sum.inl i) j + 0 + 0; simp
      · ext r; show z.2 (Sum.inr ()) r + u₀ r = z.2 (Sum.inr ()) r + 0 + u₀ r; simp
      · ext r; show z.1 r (Sum.inr ()) + y₀ r = z.1 r (Sum.inr ()) + y₀ r + 0; simp
    rw [LinearMap.comp_apply, h3, ← LinearMap.comp_apply (f := L), transY, ← LinearMap.comp_apply (f := L), transU]
    rfl
  obtain ⟨l₀, hl₀⟩ := GlobalTheory.T.translationInvariant_schwartzBruhat_map_factors_integral k ν hν X₀ n n M L' hL'
  refine ⟨l₀, fun Ψ₁ Ψ₂ => ?_⟩
  obtain ⟨Ψ, hΨ, hLΨ⟩ := hl₀ (comapH e.symm (mulLC _ hχ (prodSB Ψ₁ Ψ₂)))
  refine ⟨Ψ, ?_, ?_⟩
  · funext p
    rw [hΨ]
    unfold contr hat
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [comapH_apply, mulLC_apply, prodSB_apply]
    have h4 : uy (e.symm (p, (u, y))) = u ⬝ᵥ y := rfl
    rw [h4, neg_one_mul]
    change (ψ (-(u ⬝ᵥ y)) : ℂ) * (Ψ₁.1 (fromCols p.1 (Matrix.of fun r _ => y r)) * Ψ₂.1 (fromRows p.2 (Matrix.of fun _ => u))) = _
    ring
  · rw [← key, ← hLΨ]
    show L _ = L _
    congr 1
    ext z
    simp only [comapH_apply, Homeomorph.symm_apply_apply]
end GlobalTheory.LocFlat
