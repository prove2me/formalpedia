-- Prove2me | solution 1 for GlobalTheory.HeckeGal.exists_unique_hchar_of_finite_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:15:27.612934+00:00
-- url     : https://prove2.me/submissions/114b4c76-b5aa-47a0-a6e6-af5a1b8e7616

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Theorems.Thm_GlobalTheory_HeckeGal_infPow_zero
import Theorems.Thm_GlobalTheory_HeckeGal_lPow_zero
import Theorems.Thm_GlobalTheory_HeckeGal_toAb_surjective
import Theorems.Thm_GlobalTheory_HeckeGal_liftAb_toAb
import Theorems.Thm_GlobalTheory_HeckeGal_continuous_liftAb
import Theorems.Thm_GlobalTheory_HeckeGal_isOpen_ker_of_pow
import Theorems.Thm_P2M_GlobalTheory_HeckeGal_continuous_of_isOpen_ker__a1c5cff15c2b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory GlobalTheory.HeckeGal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.HeckeGal
theorem _root_.solution {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* (Qbar l)ˣ) (hr : Continuous r) {m : ℕ} (hm : 0 < m) (h : r ^ m = 1) :
    ∃! χ : HChar E, χ.OrderDvd m ∧ IsLAdicOf art ι χ 0 r := by
  let ψ : Ideles E →* (Qbar l)ˣ := (liftAb r hr).comp art
  have hψ : Continuous ψ := (continuous_liftAb r hr).comp ha.quot.continuous
  have hψm : ∀ x, ψ x ^ m = 1 := fun x => by
    obtain ⟨τ, hτ⟩ := toAb_surjective (art x)
    show liftAb r hr (art x) ^ m = 1
    rw [← hτ, liftAb_toAb]
    exact DFunLike.congr_fun h τ
  let χ0 : Ideles E →* ℂˣ := (Units.map ι.toRingHom.toMonoidHom).comp ψ
  have hopen : IsOpen (χ0.ker : Set (Ideles E)) :=
    Subgroup.isOpen_mono (fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [MonoidHom.comp_apply, hx, map_one]) (isOpen_ker_of_pow ψ hψ hm hψm)
  have htriv : ∀ k : Eˣ, χ0 (diagUnits E k) = 1 := fun k => by
    have hk : diagUnits E k ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    show Units.map _ (liftAb r hr (art (diagUnits E k))) = 1
    rw [MonoidHom.mem_ker.mp hk, map_one, map_one]
  refine ⟨⟨χ0, continuous_of_isOpen_ker' χ0 hopen, htriv⟩, ⟨?_, ?_⟩, ?_⟩
  · apply Subtype.ext
    refine MonoidHom.ext fun x => ?_
    show (Units.map _ (ψ x)) ^ m = 1
    rw [← map_pow, hψm, map_one]
  · intro x σ hx
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one]
    show _ = ι.symm (ι ((liftAb r hr (art x) : (Qbar l)ˣ) : Qbar l))
    rw [hx, liftAb_toAb, ι.symm_apply_apply]
  · rintro χ ⟨-, hχ⟩
    apply Subtype.ext
    refine MonoidHom.ext fun x => Units.ext ?_
    obtain ⟨τ, hτ⟩ := toAb_surjective (art x)
    have e := hχ x τ hτ.symm
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one] at e
    show _ = ι ((liftAb r hr (art x) : (Qbar l)ˣ) : Qbar l)
    rw [← hτ, liftAb_toAb, e, ι.apply_symm_apply]
end GlobalTheory.HeckeGal
