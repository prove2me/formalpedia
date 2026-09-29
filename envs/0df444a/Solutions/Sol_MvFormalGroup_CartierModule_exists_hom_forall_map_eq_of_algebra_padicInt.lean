-- Prove2me | solution 1 for MvFormalGroup.CartierModule.exists_hom_forall_map_eq_of_algebra_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/7a4abd2f-c2da-56cf-b278-a47948a4de62

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Theorems.Thm_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_homothety_add
import Theorems.Thm_MvFormalGroup_CartierModule_exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_surjective_of_algebra_padicInt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_algebra_padicInt
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

noncomputable section

namespace FullLaw

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] [Algebra (PadicInt p) R]
  {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]

set_option quotPrecheck false in
local notation "VV" => (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))

theorem iterV_add (n : ℕ) (x y : CartierModule p Φ) : VV^[n] (x + y) = VV^[n] x + VV^[n] y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_add]

theorem iterV_zero (n : ℕ) : VV^[n] (0 : CartierModule p Φ) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_zero]

theorem iterV_sub (n : ℕ) (x y : CartierModule p Φ) : VV^[n] (x - y) = VV^[n] x - VV^[n] y := by
  have := iterV_add (p := p) (Φ := Φ) n (x - y) y
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

theorem iterV_sum {ι : Type*} (s : Finset ι) (n : ℕ) (g : ι → CartierModule p Φ) :
    VV^[n] (∑ i ∈ s, g i) = ∑ i ∈ s, VV^[n] (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, iterV_add, ih]

variable (f : Fin d → CartierModule p Φ)
  (hf : ∀ i j, tangent (f i) j = if i = j then 1 else 0)

include hf in

theorem tangent_sum_homothety (t : Fin d → R) :
    tangent (∑ l : Fin d, homothety (t l) (f l)) = t := by
  classical
  funext j
  rw [map_sum, Finset.sum_apply]
  simp only [tangent_homothety, Pi.smul_apply, smul_eq_mul, hf]
  rw [Fintype.sum_eq_single j (fun l hl => by rw [if_neg hl, mul_zero]), if_pos rfl, mul_one]

include hf in

theorem exists_step (x : CartierModule p Φ) :
    ∃ y : CartierModule p Φ, x = (∑ l : Fin d, homothety (tangent x l) (f l)) + verschiebungInt y := by
  have h0 : tangent (x - ∑ l : Fin d, homothety (tangent x l) (f l)) = 0 := by
    rw [map_sub, tangent_sum_homothety f hf, sub_self]
  obtain ⟨y, hy⟩ :=
    MvFormalGroup.CartierModule.exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt
      p Φ _ h0
  exact ⟨y, by rw [hy, add_sub_cancel]⟩

def quot (x : CartierModule p Φ) : ℕ → CartierModule p Φ
  | 0 => x
  | m + 1 => (exists_step f hf (quot x m)).choose

theorem quot_zero (x : CartierModule p Φ) : quot f hf x 0 = x := rfl

theorem quot_succ (x : CartierModule p Φ) (m : ℕ) :
    quot f hf x m = (∑ l : Fin d, homothety (tangent (quot f hf x m) l) (f l)) +
      verschiebungInt (quot f hf x (m + 1)) :=
  (exists_step f hf (quot f hf x m)).choose_spec

include hf in

theorem expansion (x : CartierModule p Φ) (N : ℕ) :
    x = (∑ m ∈ Finset.range N, VV^[m]
          (∑ l : Fin d, homothety (tangent (quot f hf x m) l) (f l))) +
        VV^[N] (quot f hf x N) := by
  induction N with
  | zero => simp [quot_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, Function.iterate_succ_apply, add_assoc, ← iterV_add,
      ← quot_succ f hf x N]
    exact ih

end FullLaw

open FullLaw in
theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R]
    [Algebra (PadicInt p) R]
    {d d' : ℕ} (Φ : MvFormalGroup d R) (Φ' : MvFormalGroup d' R) [Φ.IsComm] [Φ'.IsComm]
    (θ : MvFormalGroup.CartierModule p Φ →+ MvFormalGroup.CartierModule p Φ')
    (hF : ∀ f, θ (MvFormalGroup.CartierModule.frobenius f) =
      MvFormalGroup.CartierModule.frobenius (θ f))
    (hV : ∀ f, θ (MvFormalGroup.CartierModule.verschiebungInt f) =
      MvFormalGroup.CartierModule.verschiebungInt (θ f))
    (hH : ∀ (a : R) f, θ (MvFormalGroup.CartierModule.homothety a f) =
      MvFormalGroup.CartierModule.homothety a (θ f)) :
    ∃ φ : Φ.Hom Φ', ∀ f, MvFormalGroup.CartierModule.map φ f = θ f := by
  classical

  have hsurj := MvFormalGroup.CartierModule.tangent_surjective_of_algebra_padicInt p Φ
  choose f hf0 using fun i : Fin d => hsurj (fun j => if i = j then (1 : R) else 0)
  have hf : ∀ i j, MvFormalGroup.CartierModule.tangent (f i) j = if i = j then 1 else 0 :=
    fun i j => by rw [hf0 i]

  have hVn : ∀ (n : ℕ) x, θ ((⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[n] x) =
      (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ')))^[n] (θ x) := by
    intro n x
    induction n generalizing x with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hV, ih]

  set c : ℕ → Fin d → Fin d → R := fun m i l =>
    MvFormalGroup.CartierModule.tangent (quot f hf (MvFormalGroup.CartierModule.frobenius (f i)) m) l
  set h : ℕ → Fin d → MvFormalGroup.CartierModule p Φ := fun N i =>
    quot f hf (MvFormalGroup.CartierModule.frobenius (f i)) N
  have hexp : ∀ (N : ℕ) (i : Fin d), MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, MvFormalGroup.CartierModule.homothety (c m i l) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i) :=
    fun N i => expansion f hf _ N

  have hexp' : ∀ (N : ℕ) (i : Fin d), MvFormalGroup.CartierModule.frobenius (θ (f i)) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ')))^[m]
          (∑ l : Fin d, MvFormalGroup.CartierModule.homothety (c m i l) (θ (f l)))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ')))^[N] (θ (h N i)) := by
    intro N i
    rw [← hF, hexp N i, map_add, map_sum, hVn]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hVn, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    exact hH _ _
  obtain ⟨φ, hφ⟩ :=
    MvFormalGroup.CartierModule.exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_homothety_add
      p Φ Φ' f hf c h hexp (fun i => θ (f i)) (fun N i => θ (h N i)) hexp'
  refine ⟨φ, fun x => ?_⟩

  set D : MvFormalGroup.CartierModule p Φ →+ MvFormalGroup.CartierModule p Φ' :=
    MvFormalGroup.CartierModule.map φ - θ
  have hDf : ∀ l, D (f l) = 0 := fun l => by
    show MvFormalGroup.CartierModule.map φ (f l) - θ (f l) = 0
    rw [hφ, sub_self]
  have hDV : ∀ (n : ℕ) y, D ((⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[n] y) =
      (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ')))^[n] (D y) := by
    intro n y
    induction n generalizing y with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      show MvFormalGroup.CartierModule.map φ _ - θ _ = _
      rw [MvFormalGroup.CartierModule.map_verschiebungInt, hV]
      exact (map_sub (MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ')) _ _).symm
  have hDH : ∀ (a : R) y, D (MvFormalGroup.CartierModule.homothety a y) =
      MvFormalGroup.CartierModule.homothety a (D y) := by
    intro a y
    show MvFormalGroup.CartierModule.map φ _ - θ _ = _
    rw [MvFormalGroup.CartierModule.map_homothety, hH]
    exact (map_sub (MvFormalGroup.CartierModule.homothety (p := p) (Φ := Φ') a) _ _).symm
  have hDx : ∀ N : ℕ, ∃ w, D x =
      (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ')))^[N] w := by
    intro N
    refine ⟨D (quot f hf x N), ?_⟩
    conv_lhs => rw [expansion f hf x N]
    rw [map_add, map_sum, hDV]
    have hz : ∀ m ∈ Finset.range N,
        D ((⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, MvFormalGroup.CartierModule.homothety
            (MvFormalGroup.CartierModule.tangent (quot f hf x m) l) (f l))) = 0 := by
      intro m _
      rw [hDV, map_sum]
      have : ∑ l : Fin d, D (MvFormalGroup.CartierModule.homothety
          (MvFormalGroup.CartierModule.tangent (quot f hf x m) l) (f l)) = 0 :=
        Finset.sum_eq_zero fun l _ => by rw [hDH, hDf, map_zero]
      rw [this, iterV_zero]
    rw [Finset.sum_eq_zero hz, zero_add]

  obtain ⟨s, hs, huniq⟩ :=
    MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
      p Φ' (fun _ => (0 : MvFormalGroup.CartierModule p Φ'))
  have hzero_sum : ∀ N : ℕ, (∑ m ∈ Finset.range N,
      (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ')))^[m]
        ((fun _ : ℕ => (0 : MvFormalGroup.CartierModule p Φ')) m)) = 0 :=
    fun N => Finset.sum_eq_zero fun m _ => iterV_zero m
  have h1 : D x = s := huniq (D x) fun N => by
    obtain ⟨w, hw⟩ := hDx N
    exact ⟨w, by rw [hzero_sum, zero_add]; exact hw⟩
  have h2 : (0 : MvFormalGroup.CartierModule p Φ') = s := huniq 0 fun N =>
    ⟨0, by rw [hzero_sum, zero_add, iterV_zero]⟩
  have hD0 : D x = 0 := h1.trans h2.symm
  have : MvFormalGroup.CartierModule.map φ x - θ x = 0 := hD0
  exact sub_eq_zero.mp this

end
end S_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_algebra_padicInt
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_algebra_padicInt (solution)
