-- Prove2me | solution 1 for MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebungInt_iterate_homothety_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/71be5971-42fa-50dd-985b-a9db898d2312

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Theorems.Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_of_algebra_padicInt
import Theorems.Thm_MvFormalGroup_CartierModule_exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebungInt_iterate_homothety_add
p2m_attr_erase "instance" "MvFormalGroup.instIsCommMapRingHom MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.CartierModule.toPowerSeries_baseChangeEqFun MvFormalGroup.toPowerSeries_map_ringHom MvFormalGroup.CartierModule.toPowerSeries_baseChangeEq MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false

universe u

noncomputable section

namespace CerednikDrinfeld
namespace VExpansion

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]

set_option quotPrecheck false in
local notation "V" => (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))

def tanMat (γ : Fin d → CartierModule p Φ) : Matrix (Fin d) (Fin d) R :=
  Matrix.of fun i k => tangent (γ i) k

theorem tangent_sum_homothety (γ : Fin d → CartierModule p Φ) (c : Fin d → R) :
    tangent (∑ i : Fin d, homothety (c i) (γ i)) = Matrix.vecMul c (tanMat γ) := by
  funext k
  rw [map_sum, Finset.sum_apply, Matrix.vecMul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tangent_homothety, Pi.smul_apply, smul_eq_mul]
  rfl

theorem tangent_iterate_verschiebungInt_succ (n : ℕ) (f : CartierModule p Φ) :
    tangent (V^[n + 1] f) = 0 := by
  rw [Function.iterate_succ_apply']
  exact tangent_verschiebungInt _

theorem sum_iterate_succ (N : ℕ) (x : Fin (N + 1) → CartierModule p Φ) :
    (∑ m : Fin (N + 1), V^[(m : ℕ)] (x m)) = x 0 + V (∑ m : Fin N, V^[(m : ℕ)] (x m.succ)) := by
  rw [Fin.sum_univ_succ, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Fin.val_succ, Function.iterate_succ_apply']

theorem existsUnique_expansion
    (hVinj : Function.Injective (MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))
    (hker : ∀ f : CartierModule p Φ, tangent f = 0 ↔
      ∃ g : CartierModule p Φ, MvFormalGroup.CartierModule.verschiebungInt g = f)
    (γ : Fin d → CartierModule p Φ) (hdet : IsUnit (tanMat γ).det) :
    ∀ (N : ℕ) (f : CartierModule p Φ), ∃! c : Fin N → Fin d → R, ∃ t : CartierModule p Φ,
      f = (∑ m : Fin N, V^[(m : ℕ)] (∑ i : Fin d, homothety (c m i) (γ i))) + V^[N] t := by
  classical
  have hT : IsUnit (tanMat γ) := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  have hinj : Function.Injective fun v : Fin d → R => Matrix.vecMul v (tanMat γ) :=
    Matrix.vecMul_injective_of_isUnit hT
  have hsurj : Function.Surjective fun v : Fin d → R => Matrix.vecMul v (tanMat γ) :=
    Matrix.vecMul_surjective_iff_isUnit.mpr hT
  intro N
  induction N with
  | zero =>
    intro f
    refine ⟨Fin.elim0, ⟨f, by simp⟩, fun c _ => funext fun i => i.elim0⟩
  | succ N ih =>
    intro f

    obtain ⟨c₀, hc₀⟩ := hsurj (tangent f)
    have htan : tangent (f - ∑ i : Fin d, homothety (c₀ i) (γ i)) = 0 := by
      rw [map_sub, tangent_sum_homothety, sub_eq_zero]
      exact hc₀.symm
    obtain ⟨g, hg⟩ := (hker _).mp htan
    obtain ⟨c, ⟨t, hct⟩, huniq⟩ := ih g
    refine ⟨Fin.cons c₀ c, ⟨t, ?_⟩, ?_⟩
    ·
      rw [sum_iterate_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [Function.iterate_succ_apply', add_assoc, ← map_add, ← hct, hg]
      abel
    ·
      rintro c' ⟨t', hct'⟩
      have h0 : c' 0 = c₀ := by
        apply hinj
        have h1 := congrArg tangent hct'
        rw [sum_iterate_succ, map_add, map_add, tangent_sum_homothety, tangent_verschiebungInt,
          tangent_iterate_verschiebungInt_succ, add_zero, add_zero] at h1
        show Matrix.vecMul (c' 0) (tanMat γ) = Matrix.vecMul c₀ (tanMat γ)
        rw [← h1]
        exact hc₀.symm
      have hrest : g = (∑ m : Fin N, V^[(m : ℕ)] (∑ i : Fin d, homothety (Fin.tail c' m i) (γ i))) +
          V^[N] t' := by
        apply hVinj
        have h1 := hct'
        rw [sum_iterate_succ, h0, Function.iterate_succ_apply', add_assoc, ← map_add] at h1
        rw [hg, h1, add_sub_cancel_left]
        rfl
      have h2 := huniq (Fin.tail c') ⟨t', hrest⟩
      rw [← Fin.cons_self_tail c', h0, h2]

end CerednikDrinfeld.VExpansion

end

theorem CerednikDrinfeld.VExpansion.existsUnique_pair
    {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]
    (hVinj : Function.Injective (MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))
    (hker : ∀ f : MvFormalGroup.CartierModule p Φ, MvFormalGroup.CartierModule.tangent f = 0 ↔
      ∃ g : MvFormalGroup.CartierModule p Φ, MvFormalGroup.CartierModule.verschiebungInt g = f)
    (γ : Fin d → MvFormalGroup.CartierModule p Φ) (hdet : IsUnit (CerednikDrinfeld.VExpansion.tanMat γ).det)
    (N : ℕ) (g : MvFormalGroup.CartierModule p Φ) :
    ∃! ch : (Fin N → Fin d → R) × MvFormalGroup.CartierModule p Φ,
      g = (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
              (∑ i : Fin d, MvFormalGroup.CartierModule.homothety (ch.1 m i) (γ i))) +
          (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] ch.2 := by
  obtain ⟨c, ⟨t, hct⟩, huniq⟩ := CerednikDrinfeld.VExpansion.existsUnique_expansion hVinj hker γ hdet N g
  refine ⟨(c, t), hct, ?_⟩
  rintro ⟨c', t'⟩ hct'
  have hc : c' = c := huniq c' ⟨t', hct'⟩
  subst hc
  have ht : t' = t := by
    have hiter : Function.Injective
        ((⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N]) :=
      Function.Injective.iterate hVinj N
    apply hiter
    have := hct'.symm.trans hct
    exact add_left_cancel this
  rw [ht]

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra (PadicInt p) R]
    {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : IsUnit (Matrix.of fun i j => MvFormalGroup.CartierModule.tangent (f i) j).det)
    (g : MvFormalGroup.CartierModule p Φ) (N : ℕ) :
    ∃! ch : (Fin N → Fin d → R) × MvFormalGroup.CartierModule p Φ,
      g = (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
              (∑ i : Fin d, MvFormalGroup.CartierModule.homothety (ch.1 m i) (f i))) +
          (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] ch.2 := by
  have hVinj := MvFormalGroup.CartierModule.verschiebungInt_injective_of_algebra_padicInt p Φ
  have hker : ∀ f : MvFormalGroup.CartierModule p Φ, MvFormalGroup.CartierModule.tangent f = 0 ↔
      ∃ g : MvFormalGroup.CartierModule p Φ, MvFormalGroup.CartierModule.verschiebungInt g = f :=
    fun f => ⟨MvFormalGroup.CartierModule.exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt p Φ f,
      fun ⟨g, hg⟩ => hg ▸ MvFormalGroup.CartierModule.tangent_verschiebungInt g⟩
  exact CerednikDrinfeld.VExpansion.existsUnique_pair hVinj hker f hf N g

end S_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebungInt_iterate_homothety_add
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebungInt_iterate_homothety_add (solution)
