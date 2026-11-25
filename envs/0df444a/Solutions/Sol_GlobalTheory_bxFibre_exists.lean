-- Prove2me | solution 1 for GlobalTheory.bxFibre_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:09:27.094087+00:00
-- url     : https://prove2.me/submissions/201922b4-ddaf-4526-88bc-48663b1c1c83

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PointsFibreProduct
import Theorems.Thm_GlobalTheory_bxFibre_exists_chart
import Theorems.Thm_GlobalTheory_bxFibre_closed
import Theorems.Thm_GlobalTheory_bxFibre_comp
import Theorems.Thm_GlobalTheory_bxFibre_inj
import Theorems.Thm_GlobalTheory_bxFibre_affine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Y : Scheme.{0}} {F P Q R : Type} [CommRing F] [CommRing P]
    [IsLocalRing P] [CommRing Q] [IsLocalRing Q] [CommRing R] [IsLocalRing R]
    (p : F →+* P) (q : F →+* Q) (f : P →+* R) [IsLocalHom f] (g : Q →+* R) [IsLocalHom g]
    (hex : ∀ a b, f a = g b → ∃! c, p c = a ∧ q c = b)
    (hinj : ∀ s t, p s = p t → q s = q t → s = t)
    (a : Spec (CommRingCat.of P) ⟶ Y) (b : Spec (CommRingCat.of Q) ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom f) ≫ a = Spec.map (CommRingCat.ofHom g) ≫ b) :
    ∃ c : Spec (CommRingCat.of F) ⟶ Y, Spec.map (CommRingCat.ofHom p) ≫ c = a ∧
      Spec.map (CommRingCat.ofHom q) ≫ c = b := by
  obtain ⟨U, hU, hmem⟩ := bxFibre_affine (a (closedPoint P))
  have hmem' : b (closedPoint Q) ∈ U := by
    rw [← bxFibre_closed g b, ← h, bxFibre_closed f a]
    exact hmem
  obtain ⟨φ, hφ⟩ := bxFibre_exists_chart hU a hmem
  obtain ⟨ψ, hψ⟩ := bxFibre_exists_chart hU b hmem'
  rw [hφ, hψ] at h ⊢
  erw [bxFibre_comp, bxFibre_comp] at h
  have h1 := bxFibre_inj hU h
  have h2 : ∀ s, ∃ c, p c = φ s ∧ q c = ψ s := fun s =>
    (hex _ _ (RingHom.congr_fun h1 s)).exists
  choose k hk hk' using h2
  let χ : Γ(Y, U) →+* F :=
    { toFun := k
      map_one' := hinj _ _ (by simp [hk]) (by simp [hk'])
      map_mul' := fun s t => hinj _ _ (by simp [hk]) (by simp [hk'])
      map_zero' := hinj _ _ (by simp [hk]) (by simp [hk'])
      map_add' := fun s t => hinj _ _ (by simp [hk]) (by simp [hk']) }
  refine ⟨Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec, ?_, ?_⟩
  · erw [bxFibre_comp]
    have : p.comp χ = φ := RingHom.ext hk
    rw [this]
  · erw [bxFibre_comp]
    have : q.comp χ = ψ := RingHom.ext hk'
    rw [this]
end GlobalTheory
