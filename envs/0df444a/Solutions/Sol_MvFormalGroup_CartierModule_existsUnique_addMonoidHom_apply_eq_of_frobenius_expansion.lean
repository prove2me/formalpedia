-- Prove2me | solution 1 for MvFormalGroup.CartierModule.existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/2aeb8447-caef-5796-8bb9-379ceb5738b6

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Theorems.Thm_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_homothety_add
import Theorems.Thm_MvFormalGroup_exists_hom_comp_eq_id_tangent_map_eq_of_isUnit_det
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebungInt_iterate_homothety_add
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup MvFormalGroup.instIsCommMapRingHom"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.CartierModule.toPowerSeries_baseChangeEqFun MvFormalGroup.toPowerSeries_map_ringHom MvFormalGroup.CartierModule.toPowerSeries_baseChangeEq MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

universe u

open MvFormalGroup MvFormalGroup.CartierModule

namespace A3Reduce

variable {p : ℕ} [hp : Fact p.Prime]

section generic

variable {R : Type u} [CommRing R] {d d' : ℕ} {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}
  [Φ.IsComm] [Φ'.IsComm]

local notation "VV" => (verschiebungInt : CartierModule p Φ →+ CartierModule p Φ)
local notation "VV'" => (verschiebungInt : CartierModule p Φ' →+ CartierModule p Φ')

theorem eq_zero_of_forall_exists_iterate (x : CartierModule p Φ)
    (hx : ∀ N : ℕ, ∃ t : CartierModule p Φ, x = (⇑VV)^[N] t) : x = 0 := by
  have h := existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add p Φ (fun _ => 0)
  refine h.unique ?_ ?_
  · intro N
    obtain ⟨t, ht⟩ := hx N
    exact ⟨t, by simpa [Function.iterate_fixed (map_zero _)] using ht⟩
  · intro N
    exact ⟨0, by simp [Function.iterate_fixed (map_zero _)]⟩

theorem eq_of_forall_sub_mem (x y : CartierModule p Φ)
    (h : ∀ N : ℕ, ∃ t : CartierModule p Φ, x - y = (⇑VV)^[N] t) : x = y :=
  sub_eq_zero.mp (eq_zero_of_forall_exists_iterate (x - y) h)

noncomputable def iterV (N : ℕ) : CartierModule p Φ →+ CartierModule p Φ where
  toFun := (⇑VV)^[N]
  map_zero' := Function.iterate_fixed (map_zero _) N
  map_add' a b := by
    induction N generalizing a b with
    | zero => rfl
    | succ N ih => simp only [Function.iterate_succ_apply', ih, map_add]

@[scoped simp] theorem iterV_apply (N : ℕ) (a : CartierModule p Φ) : iterV (p := p) (Φ := Φ) N a = (⇑VV)^[N] a :=
  rfl

theorem iterate_V_sub (N : ℕ) (a b : CartierModule p Φ) :
    (⇑VV)^[N] a - (⇑VV)^[N] b = (⇑VV)^[N] (a - b) := by
  rw [← iterV_apply, ← iterV_apply, ← iterV_apply, map_sub]

theorem iterate_V_add (N : ℕ) (a b : CartierModule p Φ) :
    (⇑VV)^[N] a + (⇑VV)^[N] b = (⇑VV)^[N] (a + b) := by
  rw [← iterV_apply, ← iterV_apply, ← iterV_apply, map_add]

theorem iterate_V_nsmul (N n : ℕ) (a : CartierModule p Φ) :
    n • (⇑VV)^[N] a = (⇑VV)^[N] (n • a) := by
  rw [← iterV_apply, ← iterV_apply, map_nsmul]

theorem iterate_V_sum {ι : Type*} (s : Finset ι) (N : ℕ) (a : ι → CartierModule p Φ) :
    ∑ i ∈ s, (⇑VV)^[N] (a i) = (⇑VV)^[N] (∑ i ∈ s, a i) := by
  simp only [← iterV_apply, map_sum]

theorem iterate_V_comm (N m : ℕ) (a : CartierModule p Φ) :
    (⇑VV)^[m] ((⇑VV)^[N] a) = (⇑VV)^[N] ((⇑VV)^[m] a) := by
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]

theorem homothety_iterate_V (N : ℕ) (b : R) (a : CartierModule p Φ) :
    homothety b ((⇑VV)^[N] a) = (⇑VV)^[N] (homothety (b ^ p ^ N) a) := by
  induction N generalizing b a with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', homothety_verschiebungInt, ih, Function.iterate_succ_apply',
      ← pow_mul, ← pow_succ']

theorem map_iterate_V (θ : CartierModule p Φ →+ CartierModule p Φ')
    (hV : ∀ f, θ (verschiebungInt f) = verschiebungInt (θ f)) (N : ℕ) (f : CartierModule p Φ) :
    θ ((⇑VV)^[N] f) = (⇑VV')^[N] (θ f) := by
  induction N generalizing f with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', hV, ih, Function.iterate_succ_apply']

theorem map_expansion {ι : Type*} [Fintype ι] (θ : CartierModule p Φ →+ CartierModule p Φ')
    (hV : ∀ f, θ (verschiebungInt f) = verschiebungInt (θ f))
    (hH : ∀ (b : R) f, θ (homothety b f) = homothety b (θ f))
    (N : ℕ) (c : Fin N → ι → R) (γ : ι → CartierModule p Φ) (h : CartierModule p Φ) :
    θ ((∑ m : Fin N, (⇑VV)^[(m : ℕ)] (∑ k : ι, homothety (c m k) (γ k))) + (⇑VV)^[N] h) =
      (∑ m : Fin N, (⇑VV')^[(m : ℕ)] (∑ k : ι, homothety (c m k) (θ (γ k)))) +
        (⇑VV')^[N] (θ h) := by
  simp only [map_add, map_sum, map_iterate_V θ hV, hH]

end generic

section uniq

variable {R : Type u} [CommRing R] [Algebra (PadicInt p) R] {d d' : ℕ} {Φ : MvFormalGroup d R}
  {Φ' : MvFormalGroup d' R} [Φ.IsComm] [Φ'.IsComm]

theorem addMonoidHom_eq_of_apply_basis_eq (γ : Fin d → CartierModule p Φ)
    (hγ : IsUnit (Matrix.of fun i j => tangent (γ i) j).det)
    (θ₁ θ₂ : CartierModule p Φ →+ CartierModule p Φ')
    (hV₁ : ∀ f, θ₁ (verschiebungInt f) = verschiebungInt (θ₁ f))
    (hH₁ : ∀ (b : R) f, θ₁ (homothety b f) = homothety b (θ₁ f))
    (hV₂ : ∀ f, θ₂ (verschiebungInt f) = verschiebungInt (θ₂ f))
    (hH₂ : ∀ (b : R) f, θ₂ (homothety b f) = homothety b (θ₂ f))
    (hγeq : ∀ i, θ₁ (γ i) = θ₂ (γ i)) : θ₁ = θ₂ := by
  refine AddMonoidHom.ext fun f => ?_
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_exists_iterate (Φ := Φ') (θ₁ f - θ₂ f) fun N => ?_
  obtain ⟨⟨e, t⟩, het, -⟩ := existsUnique_eq_sum_verschiebungInt_iterate_homothety_add p Φ γ hγ f N
  refine ⟨θ₁ t - θ₂ t, ?_⟩
  have h1 := congrArg θ₁ het
  have h2 := congrArg θ₂ het
  rw [map_expansion θ₁ hV₁ hH₁] at h1
  rw [map_expansion θ₂ hV₂ hH₂] at h2
  have hs : (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := Φ')))^[(m : ℕ)]
        (∑ k : Fin d, homothety (e m k) (θ₁ (γ k)))) =
      ∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := Φ')))^[(m : ℕ)]
        (∑ k : Fin d, homothety (e m k) (θ₂ (γ k))) := by
    simp only [hγeq]
  rw [h1, h2, hs, add_sub_add_left_eq_sub, iterate_V_sub]

end uniq

end A3Reduce
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion.A3Reduce"

open A3Reduce

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra (PadicInt p) R]
    {d d' : ℕ} (Φ : MvFormalGroup d R) (Φ' : MvFormalGroup d' R) [Φ.IsComm] [Φ'.IsComm]
    (γ : Fin d → MvFormalGroup.CartierModule p Φ)
    (hγ : IsUnit (Matrix.of fun i j => MvFormalGroup.CartierModule.tangent (γ i) j).det)
    (γ' : Fin d → MvFormalGroup.CartierModule p Φ')
    (c : ℕ → Fin d → Fin d → R)
    (hF : ∀ (i : Fin d) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p Φ,
      MvFormalGroup.CartierModule.frobenius (γ i) =
        (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
          (∑ k : Fin d, MvFormalGroup.CartierModule.homothety (c m i k) (γ k))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] h)
    (hF' : ∀ (i : Fin d) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p Φ',
      MvFormalGroup.CartierModule.frobenius (γ' i) =
        (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ')))^[(m : ℕ)]
          (∑ k : Fin d, MvFormalGroup.CartierModule.homothety (c m i k) (γ' k))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ')))^[N] h) :
    ∃! θ : MvFormalGroup.CartierModule p Φ →+ MvFormalGroup.CartierModule p Φ',
      (∀ i, θ (γ i) = γ' i) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.verschiebungInt f) =
        MvFormalGroup.CartierModule.verschiebungInt (θ f)) ∧
      (∀ (b : R) f, θ (MvFormalGroup.CartierModule.homothety b f) =
        MvFormalGroup.CartierModule.homothety b (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.frobenius f) =
        MvFormalGroup.CartierModule.frobenius (θ f)) := by
  classical

  obtain ⟨Ψ, instΨ, φ, ψ, hφψ, hψφ, hstd⟩ :=
    MvFormalGroup.exists_hom_comp_eq_id_tangent_map_eq_of_isUnit_det p Φ γ hγ

  choose h hh using hF
  choose h' hh' using hF'

  have hexpf : ∀ (N : ℕ) (i : Fin d),
      MvFormalGroup.CartierModule.frobenius (MvFormalGroup.CartierModule.map φ (γ i)) =
        (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Ψ)))^[m]
            (∑ l : Fin d, MvFormalGroup.CartierModule.homothety (c m i l)
              (MvFormalGroup.CartierModule.map φ (γ l)))) +
          (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Ψ)))^[N]
            (MvFormalGroup.CartierModule.map φ (h i N)) := by
    intro N i
    rw [← map_frobenius, hh i N, map_expansion (map φ) (map_verschiebungInt φ) (map_homothety φ),
      ← Fin.sum_univ_eq_sum_range]
  have hexpg : ∀ (N : ℕ) (i : Fin d),
      MvFormalGroup.CartierModule.frobenius (γ' i) =
        (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ')))^[m]
            (∑ l : Fin d, MvFormalGroup.CartierModule.homothety (c m i l) (γ' l))) +
          (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ')))^[N] (h' i N) := by
    intro N i
    rw [hh' i N, ← Fin.sum_univ_eq_sum_range]
  obtain ⟨χ, hχ⟩ :=
    MvFormalGroup.CartierModule.exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_homothety_add
      p Ψ Φ' (fun i => MvFormalGroup.CartierModule.map φ (γ i)) hstd c (fun N i => map φ (h i N)) hexpf
      γ' (fun N i => h' i N) hexpg
  refine ⟨MvFormalGroup.CartierModule.map (χ.comp φ), ⟨fun i => by rw [map_comp, hχ],
    fun f => map_verschiebungInt _ _, fun b f => map_homothety _ _ _, fun f => map_frobenius _ _⟩, ?_⟩
  rintro θ ⟨hθγ, hθV, hθH, -⟩
  refine addMonoidHom_eq_of_apply_basis_eq γ hγ θ _ hθV hθH (fun f => map_verschiebungInt _ _)
    (fun b f => map_homothety _ _ _) fun i => ?_
  rw [hθγ, map_comp, hχ]

end S_MvFormalGroup_CartierModule_existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion (solution)
