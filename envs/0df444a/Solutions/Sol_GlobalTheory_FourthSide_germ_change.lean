-- Prove2me | solution 1 for GlobalTheory.FourthSide.germ_change
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:20.702804+00:00
-- url     : https://prove2.me/submissions/53940b03-932a-4267-b7fc-502e15cb88de

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFourthSide
import Theorems.Thm_GlobalTheory_FourthSide_gm_pull_g
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FourthSide
variable {B B' G G' Ge Ge' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {L' : LB G'}
  {Φ : B' ⟶ B} {Ψ : G' ⟶ G} {pG : Ge ⟶ B} {pG' : Ge' ⟶ B'} {fG : Ge ⟶ G} {fG' : Ge' ⟶ G'} {h : Ge' ⟶ Ge}
namespace GlobalTheory.FourthSide
theorem _root_.solution (e₁ : pG' ≫ Φ = h ≫ pG) (e₂ : h ≫ fG = fG' ≫ Ψ) {w : LB.Iso M' (M.pull Φ)}
    {wL : LB.Iso L' (L.pull Ψ)} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : PGen w) (hwL : PGen wL) (hwe : PGen we)
    {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM kM : M.ι) (jM' kM' : M'.ι) (jL kL : L.ι) (jL' kL' : L'.ι)
    (a₁ : Φ (pG' (r z)) ∈ M.U jM) (a₂ : pG' (r z) ∈ M'.U jM') (a₃ : Ψ (fG' (r z)) ∈ L.U jL)
    (a₄ : fG' (r z) ∈ L'.U jL') (b₁ : Φ (pG' (r z)) ∈ M.U kM) (b₂ : pG' (r z) ∈ M'.U kM')
    (b₃ : Ψ (fG' (r z)) ∈ L.U kL) (b₄ : fG' (r z) ∈ L'.U kL') :
    germ pG' fG' h w wL we r z jM jM' jL jL' =
      gm (r ≫ pG') z _ (M'.g jM' kM') * (gm (r ≫ fG') z _ (L'.g jL' kL'))⁻¹ *
        germ pG' fG' h w wL we r z kM kM' kL kL' := by
  have p₁ : pG (h (r z)) = Φ (pG' (r z)) := congrArg (fun g => g (r z)) e₁.symm
  have p₂ : fG (h (r z)) = Ψ (fG' (r z)) := congrArg (fun g => g (r z)) e₂
  have c₃ : fG (h (r z)) ∈ L.U jL := p₂ ▸ a₃
  have d₃ : fG (h (r z)) ∈ L.U kL := p₂ ▸ b₃
  have c₁ : pG (h (r z)) ∈ M.U jM := p₁ ▸ a₁
  have d₁ : pG (h (r z)) ∈ M.U kM := p₁ ▸ b₁
  have a := hw Z (r ≫ pG') z jM kM jM' kM' a₁ b₁ a₂ b₂
  have b := hwL Z (r ≫ fG') z jL kL jL' kL' a₃ b₃ a₄ b₄
  have c := hwe Z (r ≫ h) z jM kM (fun _ => jL) (fun _ => kL) c₁ d₁ (mem_pull.2 c₃) (mem_pull.2 d₃)
  rw [gm_pull_g L fG (r ≫ h) z jL kL c₃ d₃, Category.assoc, Category.assoc, ← e₁, e₂] at c
  rw [Category.assoc] at a b
  unfold germ
  rw [a, b, c]
  generalize gm (r ≫ pG' ≫ Φ) z _ (M.g jM kM) = A
  generalize gm (r ≫ fG' ≫ Ψ) z _ (L.g jL kL) = C
  generalize gm (r ≫ pG') z _ (M'.g jM' kM') = A'
  generalize gm (r ≫ fG') z _ (L'.g jL' kL') = C'
  generalize gw w (r ≫ pG') z kM kM' = P
  generalize gw wL (r ≫ fG') z kL kL' = Q
  generalize gw we (r ≫ h) z kM (fun _ => kL) = R
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end GlobalTheory.FourthSide
