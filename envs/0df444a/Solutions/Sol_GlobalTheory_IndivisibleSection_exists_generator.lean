-- Prove2me | solution 1 for GlobalTheory.IndivisibleSection.exists_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:42:44.15226+00:00
-- url     : https://prove2.me/submissions/4aebf86c-2979-4c45-9ae7-dfe088c4406a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsGeneratorOfBasis
import Theorems.Thm_GlobalTheory_IndivisibleSection_exists_pull_chart
import Theorems.Thm_GlobalTheory_IndivisibleSection_exists_generator_of_basis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_eq_top_of_closedPoint_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndivisibleSection
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.IndivisibleSection
theorem _root_.solution (hS : SecBaseChangeSt) [IsLocalRing R] [IsNoetherianRing R] :
    ∃ b : D.SecB 1 0, ∀ s : D.SecB 1 0, ∃! a : R, SecIsMul D.P.A.hom a s b := by
  unfold SecBaseChangeSt at hS
  obtain ⟨V, hV, b, hb⟩ := hS (Sp R) D.P 1 le_rfl (IsLocalRing.closedPoint R)
  obtain rfl := DVR.eq_top_of_closedPoint_mem V hV
  have hex : ∀ i, ∃ s' : (LPow D.P.A D.P.L (↑(1 : ℕ)) (baseAt (Sp R).topIso.inv)).Sec,
      ∀ j (le : LB.wchart D.P.L (fun _ : Fin 1 => (snd (baseAt (Sp R).topIso.inv) D.P.A).left) j ≤
        (homAt (Sp R).topIso.inv ▷ D.P.A).left ⁻¹ᵁ LB.wchart D.P.L (fun _ : Fin 1 => (snd _ D.P.A).left) j),
        s'.f j = ((baseAt (Sp R).topIso.inv ⊗ D.P.A).left.presheaf.map (homOfLE le).op).hom
          (((homAt (Sp R).topIso.inv ▷ D.P.A).left.app _).hom ((b i).f j)) := fun i =>
    exists_pull_chart (K := Fin 1) (φ := fun _ => (snd _ D.P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) (b i)
      (homAt (Sp R).topIso.inv ▷ D.P.A).left (fun _ => (snd (baseAt (Sp R).topIso.inv) D.P.A).left)
      (fun _ => congrArg (fun g => g.left) (whiskerRight_snd (homAt (Sp R).topIso.inv) D.P.A))
  choose b' hb' using hex
  obtain ⟨hli, hsp⟩ := hb R (Sp R).topIso.inv b' (fun i => by
    unfold IsPullSec
    intro j
    exact hb' i j _)
  have hpos : 0 < 1 ^ D.P.g := by simp
  let i0 : Fin (1 ^ D.P.g) := ⟨0, hpos⟩
  have hone : ∀ i : Fin (1 ^ D.P.g), i = i0 := fun i => Fin.ext (by
    have hi : (i : ℕ) < 1 := lt_of_lt_of_eq i.isLt (_root_.one_pow _)
    show i.val = 0
    omega)
  have : Subsingleton (Fin (1 ^ D.P.g)) := ⟨fun x y => (hone x).trans (hone y).symm⟩
  refine exists_generator_of_basis D _ ?_ (b' i0) ?_ ?_
  · unfold overRes baseOver
    simp
  · intro r hr
    exact Fintype.linearIndependent_iff.mp hli (fun _ => r) (by rw [Fintype.sum_subsingleton _ i0]; exact hr) i0
  · intro s
    have hs := (Submodule.eq_top_iff'.mp hsp) s
    have hr : Set.range (fun i => SecM.ofSec D.P.A (b' i)) = {SecM.ofSec D.P.A (b' i0)} := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        rw [hone y]
        rfl
      · intro h
        exact ⟨i0, h.symm⟩
    rw [hr] at hs
    exact Submodule.mem_span_singleton.mp hs
end GlobalTheory.IndivisibleSection
