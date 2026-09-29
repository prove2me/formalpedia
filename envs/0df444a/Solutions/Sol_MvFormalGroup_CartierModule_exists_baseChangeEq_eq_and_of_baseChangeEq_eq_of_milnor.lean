-- Prove2me | solution 1 for MvFormalGroup.CartierModule.exists_baseChangeEq_eq_and_of_baseChangeEq_eq_of_milnor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/525421da-663d-5710-a520-be68a9e9e09e

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_exists_baseChangeEq_eq_and_of_baseChangeEq_eq_of_milnor

set_option autoImplicit false

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map toPowerSeries constantCoeff_eq_zero CartierModule CartierModule.ext toPowerSeries_map_ringHom CartierModule.baseChangeEq"
namespace CartierModule
p2m_export "MvFormalGroup.CartierModule" "ext inBlk inBlk_apply constantCoeff_inBlk subst_addFam toPowerSeries_zero map toPowerSeries constantCoeff_eq_zero baseChangeEqFun baseChangeEq toPowerSeries_baseChangeEq"
namespace MilnorKit
p2m_open "MvFormalGroup.CartierModule MvFormalGroup"

p2m_open "MvPowerSeries MvFormalGroup P2MW.S_MvFormalGroup_CartierModule_exists_baseChangeEq_eq_and_of_baseChangeEq_eq_of_milnor.MvFormalGroup MvFormalGroup.WittLaw MvFormalGroup.CartierModule P2MW.S_MvFormalGroup_CartierModule_exists_baseChangeEq_eq_and_of_baseChangeEq_eq_of_milnor.MvFormalGroup.CartierModule"

variable {p : ℕ} [hp : Fact p.Prime] {d : ℕ} {R S : Type} [CommRing R] [CommRing S]

omit hp in

theorem mvPowerSeries_eq_of_map_eq {σ : Type} {S' : Type} [CommRing S'] (q₀ : R →+* S) (q₁ : R →+* S')
    (hinj : ∀ b : R, q₀ b = 0 → q₁ b = 0 → b = 0) (φ ψ : MvPowerSeries σ R)
    (h₀ : MvPowerSeries.map q₀ φ = MvPowerSeries.map q₀ ψ)
    (h₁ : MvPowerSeries.map q₁ φ = MvPowerSeries.map q₁ ψ) : φ = ψ := by
  ext n
  rw [← sub_eq_zero]
  apply hinj
  · rw [map_sub, sub_eq_zero, ← coeff_map, ← coeff_map, h₀]
  · rw [map_sub, sub_eq_zero, ← coeff_map, ← coeff_map, h₁]

theorem map_subst_addFam (f : R →+* S) (a : Fin d → MvPowerSeries ℕ R) (j : Fin d) :
    MvPowerSeries.map f (subst (addFam p R) (a j)) = subst (addFam p S) (MvPowerSeries.map f (a j)) := by
  rw [map_subst (hasSubst_addFam p R)]
  have hA : (fun n => MvPowerSeries.map f (addFam p R n)) = addFam p S := funext (map_addFam f)
  rw [hA]

theorem map_subst_inBlk (f : R →+* S) (a : Fin d → MvPowerSeries ℕ R) (ha : ∀ l, (a l).constantCoeff = 0)
    (Φ : MvFormalGroup d R) (j : Fin d) :
    MvPowerSeries.map f (subst (Sum.elim (inBlk 0 a) (inBlk 1 a)) (Φ.toPowerSeries j)) =
      subst (Sum.elim (inBlk 0 (fun l => MvPowerSeries.map f (a l))) (inBlk 1 (fun l => MvPowerSeries.map f (a l))))
        ((Φ.map f).toPowerSeries j) := by
  have hE : HasSubst (Sum.elim (inBlk 0 a) (inBlk 1 a)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (l | l)
    · exact constantCoeff_inBlk 0 ha l
    · exact constantCoeff_inBlk 1 ha l
  rw [map_subst hE, toPowerSeries_map_ringHom]
  have hblk : ∀ (i : Fin 2) (l : Fin d), MvPowerSeries.map f (inBlk i a l) =
      inBlk i (fun l => MvPowerSeries.map f (a l)) l := by
    intro i l
    rw [inBlk_apply, inBlk_apply, map_subst (hasSubst_blk i)]
    congr 1
    funext n
    exact map_X f (i, n)
  have hfam : (fun s => MvPowerSeries.map f (Sum.elim (inBlk 0 a) (inBlk 1 a) s)) =
      Sum.elim (inBlk 0 fun l => MvPowerSeries.map f (a l)) (inBlk 1 fun l => MvPowerSeries.map f (a l)) := by
    funext s
    rcases s with l | l
    · exact hblk 0 l
    · exact hblk 1 l
  rw [hfam]

end MvFormalGroup.CartierModule.MilnorKit

p2m_open "MvPowerSeries MvFormalGroup P2MW.S_MvFormalGroup_CartierModule_exists_baseChangeEq_eq_and_of_baseChangeEq_eq_of_milnor.MvFormalGroup MvFormalGroup.WittLaw MvFormalGroup.CartierModule P2MW.S_MvFormalGroup_CartierModule_exists_baseChangeEq_eq_and_of_baseChangeEq_eq_of_milnor.MvFormalGroup.CartierModule P2MW.S_MvFormalGroup_CartierModule_exists_baseChangeEq_eq_and_of_baseChangeEq_eq_of_milnor.MvFormalGroup.CartierModule.MilnorKit"

theorem solution
    (p : ℕ) [Fact p.Prime] {d : ℕ}
    {B B₀ B₁ B₀₁ : Type} [CommRing B] [CommRing B₀] [CommRing B₁] [CommRing B₀₁]
    (q₀ : B →+* B₀) (q₁ : B →+* B₁) (r₀ : B₀ →+* B₀₁) (r₁ : B₁ →+* B₀₁)
    (hsq : r₀.comp q₀ = r₁.comp q₁)
    (hinj : ∀ b : B, q₀ b = 0 → q₁ b = 0 → b = 0)
    (hglue : ∀ (b₀ : B₀) (b₁ : B₁), r₀ b₀ = r₁ b₁ → ∃ b : B, q₀ b = b₀ ∧ q₁ b = b₁)
    (Φ : MvFormalGroup d B) [Φ.IsComm]
    (Φ₀ : MvFormalGroup d B₀) [Φ₀.IsComm] (h₀ : Φ.map q₀ = Φ₀)
    (Φ₁ : MvFormalGroup d B₁) [Φ₁.IsComm] (h₁ : Φ.map q₁ = Φ₁)
    (Ψ : MvFormalGroup d B₀₁) [Ψ.IsComm] (h₀' : Φ₀.map r₀ = Ψ) (h₁' : Φ₁.map r₁ = Ψ) :
    (∀ m : MvFormalGroup.CartierModule p Φ,
        MvFormalGroup.CartierModule.baseChangeEq q₀ h₀ m = 0 →
        MvFormalGroup.CartierModule.baseChangeEq q₁ h₁ m = 0 → m = 0) ∧
    (∀ (m₀ : MvFormalGroup.CartierModule p Φ₀) (m₁ : MvFormalGroup.CartierModule p Φ₁),
        MvFormalGroup.CartierModule.baseChangeEq r₀ h₀' m₀ = MvFormalGroup.CartierModule.baseChangeEq r₁ h₁' m₁ →
        ∃ m : MvFormalGroup.CartierModule p Φ,
          MvFormalGroup.CartierModule.baseChangeEq q₀ h₀ m = m₀ ∧
          MvFormalGroup.CartierModule.baseChangeEq q₁ h₁ m = m₁) := by
  classical
  refine ⟨?_, ?_⟩
  ·
    intro m hm₀ hm₁
    apply CartierModule.ext
    funext j
    have e₀ := congrArg (fun c : MvFormalGroup.CartierModule p Φ₀ => c.toPowerSeries j) hm₀
    have e₁ := congrArg (fun c : MvFormalGroup.CartierModule p Φ₁ => c.toPowerSeries j) hm₁
    simp only [toPowerSeries_baseChangeEq, toPowerSeries_zero] at e₀ e₁
    rw [toPowerSeries_zero]
    exact mvPowerSeries_eq_of_map_eq q₀ q₁ hinj _ _ (by rw [e₀, map_zero]) (by rw [e₁, map_zero])
  ·
    intro m₀ m₁ hcomp
    have hc : ∀ (j : Fin d) (n : ℕ →₀ ℕ), r₀ (coeff n (m₀.toPowerSeries j)) = r₁ (coeff n (m₁.toPowerSeries j)) := by
      intro j n
      have e := congrArg (fun c : MvFormalGroup.CartierModule p Ψ => coeff n (c.toPowerSeries j)) hcomp
      simpa only [toPowerSeries_baseChangeEq, coeff_map] using e
    choose s hs₀ hs₁ using fun (j : Fin d) (n : ℕ →₀ ℕ) => hglue _ _ (hc j n)

    have hS₀ : ∀ j, MvPowerSeries.map q₀ (s j) = m₀.toPowerSeries j := fun j => by
      ext n; rw [coeff_map]; exact hs₀ j n
    have hS₁ : ∀ j, MvPowerSeries.map q₁ (s j) = m₁.toPowerSeries j := fun j => by
      ext n; rw [coeff_map]; exact hs₁ j n
    have hs_const : ∀ j, MvPowerSeries.constantCoeff (σ := ℕ) (R := B) (s j) = 0 := by
      intro j
      apply hinj
      · rw [← constantCoeff_map, hS₀]; exact m₀.constantCoeff_eq_zero j
      · rw [← constantCoeff_map, hS₁]; exact m₁.constantCoeff_eq_zero j
    have hfam₀ : (fun l => MvPowerSeries.map q₀ (s l)) = m₀.toPowerSeries := funext hS₀
    have hfam₁ : (fun l => MvPowerSeries.map q₁ (s l)) = m₁.toPowerSeries := funext hS₁
    refine ⟨⟨s, hs_const, fun j => ?_⟩, ?_, ?_⟩
    · show subst (addFam p B) (s j) = subst (Sum.elim (inBlk 0 s) (inBlk 1 s)) (Φ.toPowerSeries j)
      apply mvPowerSeries_eq_of_map_eq q₀ q₁ hinj
      · rw [map_subst_addFam, map_subst_inBlk q₀ s hs_const Φ j, hfam₀, hS₀, h₀]
        exact m₀.subst_addFam j
      · rw [map_subst_addFam, map_subst_inBlk q₁ s hs_const Φ j, hfam₁, hS₁, h₁]
        exact m₁.subst_addFam j
    · apply CartierModule.ext; funext j
      rw [toPowerSeries_baseChangeEq]; exact hS₀ j
    · apply CartierModule.ext; funext j
      rw [toPowerSeries_baseChangeEq]; exact hS₁ j

end S_MvFormalGroup_CartierModule_exists_baseChangeEq_eq_and_of_baseChangeEq_eq_of_milnor
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_exists_baseChangeEq_eq_and_of_baseChangeEq_eq_of_milnor (solution)
