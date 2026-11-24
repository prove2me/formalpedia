-- Prove2me | solution 1 for GlobalTheory.PowSec.exists_basis_sections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:08:37.362772+00:00
-- url     : https://prove2.me/submissions/443de45e-56aa-406a-b77c-611d80016b53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsBasisOfIsField
import Theorems.Thm_GlobalTheory_PowSec_down_surjective
import Theorems.Thm_GlobalTheory_PowSec_exists_basis_of_isField
import Theorems.Thm_GlobalTheory_PowSec_appLE_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.PowSec
attribute [local instance] Over.cartesianMonoidalCategory
open Out
namespace GlobalTheory.PowSec
theorem _root_.solution (H : Out.GlobalSectionsRankAlgClosed) (K : Type) [Field K] [IsAlgClosed K]
    (P : Out.PolAV (Sp K)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ s : Fin (n ^ P.g) → (lbPow P.L n).Sec, ∀ t : (lbPow P.L n).Sec,
      ∃! a : Fin (n ^ P.g) → K, ∀ j, t.f j = ∑ i, constFn P.A.hom _ (a i) * (s i).f j := by
  have hr := H K P n hn
  let T : Over (Sp K) := baseOver (Sp K)
  let c : Γ(T.left, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have hfield : IsField Γ(T.left, ⊤) := c.toMulEquiv.isField (Field.toIsField K)
  obtain ⟨b⟩ := exists_basis_of_isField (R := Γ(T.left, ⊤)) (M := SecM P.A P.L n T) hfield (pow_pos hn _) hr
  let ρ : P.A ⟶ T ⊗ P.A := lift (Over.homMk P.A.hom (Category.comp_id _)) (𝟙 _)
  have ρ₂ : ρ.left ≫ (snd T P.A).left = 𝟙 _ := congrArg (fun q => q.left) (lift_snd _ _ : ρ ≫ _ = _)
  have ρ₁ : ρ.left ≫ (fst T P.A).left = P.A.hom := congrArg (fun q => q.left) (lift_fst _ _ : ρ ≫ _ = _)
  have ρ₃ : (snd T P.A).left ≫ ρ.left = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans (pullback.condition.symm.trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  haveI : IsIso ρ.left := ⟨_, ρ₂, ρ₃⟩
  let D : SecM P.A P.L n T → (lbPow P.L n).Sec := fun v =>
    down P.L (snd T P.A).left ρ.left ρ₂ n (SecM.toSec P.A v)
  have hlin : ∀ (a : Fin (n ^ P.g) → K) j,
      (D (∑ i, c.symm (a i) • b i)).f j = ∑ i, constFn P.A.hom _ (a i) * (D (b i)).f j := by
    intro a j
    show (ρ.left.appLE _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ j).le).hom
      ((∑ i, c.symm (a i) • b i : SecM P.A P.L n T).1 (fun _ => j PUnit.unit)) = _
    rw [Submodule.coe_sum]
    refine (congrArg _ (Finset.sum_apply _ _ _)).trans ?_
    refine (map_sum (ρ.left.appLE _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ j).le).hom _ _).trans
      (Finset.sum_congr rfl fun i _ => ?_)
    refine (map_mul _ (liftHom P.A _ (c.symm (a i))) ((b i).1 fun _ => j PUnit.unit)).trans (congrArg₂ (· * ·) ?_ rfl)
    have h1 := (Scheme.Hom.appLE_comp_appLE ρ.left (fst T P.A).left ⊤ _ _ (fun _ _ => trivial)
      (chart_eq P.L (snd T P.A).left ρ.left ρ₂ j).le).trans (appLE_congr ρ₁ ⊤ _ _ (fun _ _ => trivial))
    exact congrArg (fun φ => φ.hom (c.symm (a i))) h1
  have hinj : ∀ v w, (∀ j, (D v).f j = (D w).f j) → v = w := by
    intro v w h
    refine Subtype.ext (funext fun j => ?_)
    obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    exact appLE_injective ρ.left _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)) (h fun _ => k)
  refine ⟨fun i => D (b i), fun t => ?_⟩
  obtain ⟨w, hw⟩ := down_surjective P.L (snd T P.A).left ρ.left ρ₂ n t
  have hw' : D (SecM.ofSec P.A w) = t := hw
  refine ⟨fun i => c (b.repr (SecM.ofSec P.A w) i), fun j => ?_, fun a ha => ?_⟩
  · rw [← hlin]
    simp only [RingEquiv.symm_apply_apply]
    rw [b.sum_repr, hw']
  · have h0 : SecM.ofSec P.A w = ∑ i, c.symm (a i) • b i :=
      hinj _ _ fun j => by rw [hw', hlin]; exact ha j
    funext i
    rw [h0, b.repr_sum_self]
    exact (c.apply_symm_apply _).symm
end GlobalTheory.PowSec
