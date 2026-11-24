-- Prove2me | solution 1 for GlobalTheory.TateTower.finite_levelIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:27:40.24491+00:00
-- url     : https://prove2.me/submissions/fd9ee497-865d-49f0-9ffb-ad513ea377e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TateIsometryOfFiniteLevelIsometries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TateTower
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {K : Type} [Field K] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}
namespace GlobalTheory.TateTower
theorem _root_.solution {N : ℕ} (hN : 0 < N) (hQ : Finite {x : Q // x ^ N = 1}) :
    {p | LevelIso D act e N p}.Finite := by
  have := D.fin
  have hf : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  obtain ⟨S, hS, hSf⟩ := AddGroup.fg_iff.1 (Module.Finite.iff_addGroup_fg.1 hf)
  have := hSf.to_subtype
  have hQ' : {x : Q | x ^ N = 1}.Finite := hQ
  have hζ : {ζ : Kˣ | ζ ^ N = 1}.Finite := by
    have : NeZero N := ⟨hN.ne'⟩
    have : Finite (rootsOfUnity N K) := inferInstance
    exact this
  refine Set.Finite.of_finite_image (f := fun p => (p.1, fun s : S => p.2 s))
    ((hζ.prod (Set.Finite.pi' (fun _ : S => hQ'))).subset ?_) ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨hp.1.pow_eq_one, fun s => (hp.2.2.2.2.1 _).2 ⟨_, rfl⟩⟩
  · intro p hp q hq h
    refine Prod.ext (Prod.ext_iff.1 h).1 (funext fun a => ?_)
    have := AddMonoidHom.eq_of_eqOn_dense hS
      (f := AddMonoidHom.mk' (fun a => Additive.ofMul (p.2 a)) hp.2.1)
      (g := AddMonoidHom.mk' (fun a => Additive.ofMul (q.2 a)) hq.2.1)
      (fun s hs => congrFun (Prod.ext_iff.1 h).2 ⟨s, hs⟩)
    exact DFunLike.congr_fun this a
end GlobalTheory.TateTower
