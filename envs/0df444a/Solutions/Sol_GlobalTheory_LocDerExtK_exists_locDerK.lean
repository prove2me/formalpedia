-- Prove2me | solution 1 for GlobalTheory.LocDerExtK.exists_locDerK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:00:53.666201+00:00
-- url     : https://prove2.me/submissions/822924c7-71c0-409f-922c-77e7fe783f7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationExtensionOfAffine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLocalDerivationAlongFibreFieldOfAffi
import Theorems.Thm_GlobalTheory_LocDerExtK_rsT_eq
import Theorems.Thm_GlobalTheory_LocDerExt_app_res
import Theorems.Thm_GlobalTheory_LocDerExt_cover
import Theorems.Thm_GlobalTheory_LocDerExt_der_exists
import Theorems.Thm_GlobalTheory_LocDerExt_der_unique
import Theorems.Thm_GlobalTheory_LocDerExt_res_const
import Theorems.Thm_GlobalTheory_LocDerExt_res_res
import Theorems.Thm_GlobalTheory_LocDerExt_sep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.LocDerExtK
open GlobalTheory.LocDerExt
namespace GlobalTheory.LocDerExtK
theorem _root_.solution : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (Y X : Scheme.{0}) (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W₀ : X.Opens), IsAffineOpen W₀ → ∀ d₀ : Γ(X, W₀) → Γ(Y, m ⁻¹ᵁ W₀), (∀ a b, d₀ (a + b) = d₀ a + d₀ b) → (∀ a b, d₀ (a * b) = (m.app W₀).hom a * d₀ b + (m.app W₀).hom b * d₀ a) → (∀ r, d₀ (constFn p W₀ r) = constFn q (m ⁻¹ᵁ W₀) (D r)) → ∃ d, LocDerK q p m D W₀ d ∧ d W₀ = d₀ := by
  intro K _ R _ Y X q p m D W₀ hW d₀ hadd hmul hbase
  have H : ∀ f : Γ(X, W₀), ∃ δ : Γ(X, X.basicOpen f) → Γ(Y, m ⁻¹ᵁ X.basicOpen f),
      (∀ a b, δ (a + b) = δ a + δ b) ∧
      (∀ a b, δ (a * b) = (m.app _).hom a * δ b + (m.app _).hom b * δ a) ∧
      ∀ a, δ (resG X (X.basicOpen_le f) a) = resG Y (pre_le m (X.basicOpen_le f)) (d₀ a) := by
    intro f
    haveI := hW.isLocalization_basicOpen f
    refine der_exists f (m.app (X.basicOpen f)).hom
      (fun a => resG Y (pre_le m (X.basicOpen_le f)) (d₀ a)) (fun a b => by simp only [hadd, map_add])
      (fun a b => ?_)
    have e : ∀ a, (m.app (X.basicOpen f)).hom (algebraMap Γ(X, W₀) Γ(X, X.basicOpen f) a) =
        resG Y (pre_le m (X.basicOpen_le f)) ((m.app W₀).hom a) :=
      fun a => app_res m (X.basicOpen_le f) a
    rw [e, e]
    simp only [hmul, map_add, map_mul]
  choose δ δadd δmul δres using H
  have compat : ∀ (f g : Γ(X, W₀)) (k : X.basicOpen g ≤ X.basicOpen f) (s : Γ(X, X.basicOpen f)),
      resG Y (pre_le m k) (δ f s) = δ g (resG X k s) := by
    intro f g k s
    haveI := hW.isLocalization_basicOpen f
    refine der_unique f ((m.app (X.basicOpen g)).hom.comp (resG X k))
      (fun s => resG Y (pre_le m k) (δ f s)) (fun s => δ g (resG X k s)) (fun a b => ?_)
      (fun a b => ?_) (fun a => ?_) s
    · simp only [δmul, map_add, map_mul, RingHom.comp_apply, app_res m k]
    · simp only [δmul, map_mul, RingHom.comp_apply]
    · change resG Y (pre_le m k) (δ f (resG X (X.basicOpen_le f) a)) =
        δ g (resG X k (resG X (X.basicOpen_le f) a))
      rw [res_res X, δres, δres, res_res Y]
  have G : ∀ (W : X.Opens), W ≤ W₀ → ∀ s : Γ(X, W), ∃ t : Γ(Y, m ⁻¹ᵁ W),
      ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG Y (pre_le m k) t = δ f (resG X k s) := by
    intro W h s
    obtain ⟨t, ht, -⟩ := Y.sheaf.existsUnique_gluing'
      (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => m ⁻¹ᵁ X.basicOpen i.1)
      (m ⁻¹ᵁ W) (fun i => homOfLE (pre_le m i.2)) (cover m hW h)
      (fun i => δ i.1 (resG X i.2 s)) (fun i j => by
        have e : X.basicOpen (i.1 * j.1) = X.basicOpen i.1 ⊓ X.basicOpen j.1 := X.basicOpen_mul _ _
        have ki : X.basicOpen (i.1 * j.1) ≤ X.basicOpen i.1 := e.le.trans inf_le_left
        have kj : X.basicOpen (i.1 * j.1) ≤ X.basicOpen j.1 := e.le.trans inf_le_right
        have k : m ⁻¹ᵁ X.basicOpen i.1 ⊓ m ⁻¹ᵁ X.basicOpen j.1 ≤ m ⁻¹ᵁ X.basicOpen (i.1 * j.1) :=
          fun y hy => e.ge hy
        have e' : resG Y (pre_le m ki) (δ i.1 (resG X i.2 s)) =
            resG Y (pre_le m kj) (δ j.1 (resG X j.2 s)) := by
          rw [compat _ _ ki, compat _ _ kj, res_res X, res_res X]
        have e'' := congrArg (resG Y k) e'
        rw [res_res Y, res_res Y] at e''
        exact e'')
    exact ⟨t, fun f k => ht ⟨f, k⟩⟩
  choose t ht using G
  classical
  refine ⟨fun W s => if h : W ≤ W₀ then t W h s else 0, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro W h a b
    simp only [dif_pos h]
    refine sep m hW h _ _ (fun f k => ?_)
    rw [map_add, ht W h _ f k, ht W h _ f k, ht W h _ f k, map_add, δadd]
  · intro W h a b
    simp only [dif_pos h]
    refine sep m hW h _ _ (fun f k => ?_)
    rw [map_add, map_mul, map_mul, ht W h _ f k, ht W h _ f k, ht W h _ f k, map_mul, δmul, app_res m k, app_res m k]
  · intro W W' h' h a
    simp only [dif_pos h, dif_pos (h'.trans h)]
    refine sep m hW (h'.trans h) _ _ (fun f k => ?_)
    rw [rsT_eq (pre_le m h')]
    refine Eq.trans ?_ (res_res Y (pre_le m h') (pre_le m k) _).symm
    rw [ht W' _ _ f k, ht W h a f (k.trans h'), res_res X]
  · intro W h r
    simp only [dif_pos h]
    refine sep m hW h _ _ (fun f k => ?_)
    rw [ht W h _ f k, res_const, res_const, ← res_const p (X.basicOpen_le f), δres, hbase, res_const]
  · funext a
    simp only [dif_pos (le_refl W₀)]
    refine sep m hW le_rfl _ _ (fun f k => ?_)
    rw [ht W₀ _ _ f k, δres]
end GlobalTheory.LocDerExtK
