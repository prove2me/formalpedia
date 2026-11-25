-- Prove2me | solution 1 for GlobalTheory.TorusTranslate.exists_point_translate_pure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:05:54.66895+00:00
-- url     : https://prove2.me/submissions/4704fc1b-4f70-469f-8043-3203fca26005

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPointTranslatePure
import Theorems.Thm_GlobalTheory_TorusTranslate_torus_comp_q
import Theorems.Thm_GlobalTheory_TorusTranslate_translate_le
import Theorems.Thm_GlobalTheory_TorusTranslate_translate_pure
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.TorusTranslate
namespace GlobalTheory.TorusTranslate
theorem _root_.solution : (∀ (k : Type) [Field k] (Φ : FibPre k) (t : Multiplicative Φ.E.X →* kˣ), ∃ a : Φ.Pt, a ≫ Φ.D.q = 1 ∧ (∀ n : ℕ, t ^ n = 1 → a ^ n = 1) ∧ ∀ (d : ℕ) (α : Φ.E.X) (φ : (Φ.H d).Sec), Φ.Pure α φ → ∀ (x : Φ.Pt) (l : Φ.N₀.ι), ⊤ ≤ x.left ⁻¹ᵁ (Φ.H d).U l → ⊤ ≤ (a * x).left ⁻¹ᵁ (Φ.H d).U l ∧ valF (a * x).left ((Φ.H d).U l) (φ.f l) = (t (Multiplicative.ofAdd α) : k) * valF x.left ((Φ.H d).U l) (φ.f l)) := by
  intro k _ Φ t
  have := Φ.D.i_hom
  let κ : kˣ →* Γ((Out.baseOver (Sp k)).left, ⊤)ˣ :=
    Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom
  let e := splitTorusPointsEquiv (Sp k) Φ.E.X (Out.baseOver (Sp k))
  let τ := e.symm (κ.comp t)
  have hτ : e τ = κ.comp t := e.apply_symm_apply _
  refine ⟨τ ≫ Φ.D.i, torus_comp_q Φ.D τ, fun n hn => ?_, fun d α φ hφ x l hx => ?_⟩
  · have : τ ^ n = 1 := by
      apply e.injective
      rw [map_pow, map_one, hτ]
      refine MonoidHom.ext fun χ => ?_
      have := DFunLike.congr_fun hn χ
      rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← map_pow, this, map_one, MonoidHom.one_apply]
    rw [← MonObj.pow_comp, this, MonObj.one_comp]
  · have hx' := translate_le Φ.D τ x (Φ.N₀.U l) hx
    refine ⟨hx', ?_⟩
    have key := translate_pure Φ.D τ x (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) α (φ.f l)
      (fun β hβ => by
        by_contra hne
        exact hβ (hφ ⟨l, hne⟩)) hx hx'
    rw [← splitTorusPointsEquiv_val] at key
    have hv : (splitTorusPointsEquiv (Sp k) Φ.E.X (Out.baseOver (Sp k)) τ
        (Multiplicative.ofAdd α)).val =
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (t (Multiplicative.ofAdd α) : k) := by
      change (e τ _).val = _
      rw [hτ]; rfl
    rw [hv] at key
    have key2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom key
    refine Eq.trans ?_ (Eq.trans key2 (Eq.trans ((map_mul _ _ _)) ?_))
    · exact dif_pos hx'
    · congr 1
      · exact Iso.inv_hom_id_apply _ _
      · symm
        exact dif_pos hx
end GlobalTheory.TorusTranslate
