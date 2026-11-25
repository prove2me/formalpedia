-- Prove2me | solution 1 for GlobalTheory.LevelFibre.inGam_of_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:35:52.459548+00:00
-- url     : https://prove2.me/submissions/480722fe-224c-463d-aded-223cbcd00d76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFibreSimplyTransitive
import Theorems.Thm_GlobalTheory_LevelFibre_level_split
import Theorems.Thm_GlobalTheory_LevelFibre_mem_of_modN
import Theorems.Thm_GlobalTheory_LevelFibre_level_pos
import Theorems.Thm_GlobalTheory_LevelFibre_modN_of_ev_eq
import Theorems.Thm_GlobalTheory_LevelFibre_ev_pow_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LevelFibre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
namespace GlobalTheory.LevelFibre
theorem _root_.solution (l l₂ : Level H) (hd : l.Dvd l₂) (J J' : TateIso D k Q act e) (g : Sim D)
    (hg : ∀ n, 0 < n → (∀ a, J'.ev n a = J.ev n (g.f n a)) ∧ J'.ζ n = J.ζ n ^ g.ν n)
    (hζ : J'.ζ l₂.A = J.ζ l₂.A) (P P' : D.La → Q)
    (hP : ∀ a b, P (a + b) = P a * P b) (hP' : ∀ a b, P' (a + b) = P' a * P' b)
    (hk : ∀ a ∈ l₂.Mb • (⊤ : Submodule (𝓞 E) D.La), P a = 1)
    (hk' : ∀ a ∈ l₂.Mb • (⊤ : Submodule (𝓞 E) D.La), P' a = 1)
    (hJ : ∀ a ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), P a = J.ev l₂.M a)
    (hJ' : ∀ a ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), P' a = J'.ev l₂.M a)
    (hM : ∀ a, P a ^ (l₂.M / l.M) = P' a ^ (l₂.M / l.M))
    (hA : ∀ a, J.ev l₂.A a ^ (l₂.A / l.A) = J'.ev l₂.A a ^ (l₂.A / l.A)) :
    g.InGam l l₂ ∧ ∀ a, P' a = P (g.f l₂.M a) := by
  obtain ⟨u, hu, v, hv, huv⟩ := level_split l₂
  have hcs : ∀ c : D.La, c = u • c + v • c := fun c => by rw [← add_smul, huv, one_smul]
  refine ⟨⟨?_, fun a => ?_, fun a => ?_⟩, fun a => ?_⟩
  · rw [← (J.ζ_prim _ l₂.A_pos).zpow_eq_one_iff_dvd, zpow_sub_one, ← (hg _ l₂.A_pos).2, hζ, mul_inv_cancel]
  · have h := hM (v • a)
    rw [hJ _ (Submodule.smul_mem_smul hv trivial), hJ' _ (Submodule.smul_mem_smul hv trivial),
      ev_pow_div J (level_pos l₂) hd.1, ev_pow_div J' (level_pos l₂) hd.1, (hg _ (level_pos l)).1] at h
    have h2 := mem_of_modN l (modN_of_ev_eq J (level_pos l) h.symm)
    rw [map_smul, ← smul_sub] at h2
    rw [hcs (g.f l.M a - a)]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul (hd.2.1 hu) trivial) h2
  · have h := hA a
    rw [ev_pow_div J l₂.A_pos hd.2.2, ev_pow_div J' l₂.A_pos hd.2.2, (hg _ l.A_pos).1] at h
    exact modN_of_ev_eq J l.A_pos h.symm
  · rw [hcs a, hP', hk' _ (Submodule.smul_mem_smul hu trivial), map_add, hP, map_smul, map_smul,
      hk _ (Submodule.smul_mem_smul hu trivial), hJ _ (Submodule.smul_mem_smul hv trivial),
      hJ' _ (Submodule.smul_mem_smul hv trivial), (hg _ (level_pos l₂)).1, map_smul]
end GlobalTheory.LevelFibre
