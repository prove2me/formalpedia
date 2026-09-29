-- Prove2me | solution 1 for LanglandsTunnell.exists_resolventSignChar_sylowH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6d803f9d-06af-5d38-85d8-3daf940638d1

import Mathlib
import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_C8Tower
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_ne_bot_forall_inertia_ne_bot_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_resolventSignChar_sylowH
set_option autoImplicit false

p2m_open "NumberField IsDedekindDomain LanglandsTunnell P2MW.S_LanglandsTunnell_exists_resolventSignChar_sylowH.LanglandsTunnell"
open scoped Pointwise

namespace Equiv p2m_export "Equiv" "symm_apply_apply permCongr_apply conj ext Perm Perm.sign permCongr mk Perm.sign_permCongr" namespace Perm p2m_export "Equiv.Perm" "ext sign sign_permCongr" end Equiv.Perm
p2m_open_scoped "Equiv Equiv.Perm" in

theorem Equiv.Perm.sign_eq_neg_one_iff_exists_period_two_fin_three :
    ∀ π : Equiv.Perm (Fin 3), (Equiv.Perm.sign π = -1 ↔ ∃ x : Fin 3, π x ≠ x ∧ π (π x) = x) := by
  decide

p2m_open_scoped "Equiv Equiv.Perm" in

theorem Equiv.Perm.eq_one_of_sign_eq_one_of_exists_fixed_fin_three :
    ∀ π : Equiv.Perm (Fin 3), Equiv.Perm.sign π = 1 → (∃ x : Fin 3, π x = x) → π = 1 := by
  decide

namespace MulAction p2m_export "MulAction" "orbit mem_orbit_iff minimalPeriod_eq_card mk Quotient.smul_mk toPermHom period mem_orbit_self mem_orbit minimalPeriod_pos" end MulAction
p2m_open_scoped "MulAction" in

theorem MulAction.ncard_orbit_zpowers_eq_two_iff {G α : Type*} [Group G] [MulAction G α] (τ : G) (x : α)
    [Finite (MulAction.orbit (Subgroup.zpowers τ) x)] :
    (MulAction.orbit (Subgroup.zpowers τ) x).ncard = 2 ↔ τ • x ≠ x ∧ τ • τ • x = x := by
  classical
  haveI : Fintype (MulAction.orbit (Subgroup.zpowers τ) x) := Fintype.ofFinite _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, ← MulAction.minimalPeriod_eq_card,
    Function.minimalPeriod_eq_prime_iff]
  simp only [Function.IsPeriodicPt, Function.IsFixedPt, Function.iterate_succ, Function.iterate_zero,
    Function.comp_apply, id_eq]
  exact and_comm

p2m_open_scoped "Equiv Equiv.Perm" in

theorem Equiv.Perm.sign_eq_neg_one_iff_exists_period_two_of_card_eq_three {X : Type*} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 3) (π : Equiv.Perm X) :
    Equiv.Perm.sign π = -1 ↔ ∃ x : X, π x ≠ x ∧ π (π x) = x := by
  obtain ⟨e⟩ : Nonempty (X ≃ Fin 3) := Fintype.card_eq.mp (by rw [hX, Fintype.card_fin])
  have hs : Equiv.Perm.sign (e.permCongr π) = Equiv.Perm.sign π := Equiv.Perm.sign_permCongr e π
  rw [← hs, Equiv.Perm.sign_eq_neg_one_iff_exists_period_two_fin_three]
  constructor
  · rintro ⟨y, hy1, hy2⟩
    refine ⟨e.symm y, fun h => hy1 ?_, ?_⟩
    · simpa [Equiv.permCongr_apply] using congrArg e h
    · have := hy2
      simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply] at this
      simpa using congrArg e.symm this
  · rintro ⟨x, hx1, hx2⟩
    refine ⟨e x, fun h => hx1 ?_, ?_⟩
    · simpa [Equiv.permCongr_apply] using h
    · simp [Equiv.permCongr_apply, hx2]

p2m_open_scoped "Equiv Equiv.Perm" in
theorem Equiv.Perm.eq_one_of_sign_eq_one_of_exists_fixed_of_card_eq_three {X : Type*} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 3) (π : Equiv.Perm X) (hπ : Equiv.Perm.sign π = 1) (hfix : ∃ x : X, π x = x) : π = 1 := by
  obtain ⟨e⟩ : Nonempty (X ≃ Fin 3) := Fintype.card_eq.mp (by rw [hX, Fintype.card_fin])
  have hs : Equiv.Perm.sign (e.permCongr π) = 1 := by rw [Equiv.Perm.sign_permCongr e π, hπ]
  obtain ⟨x, hx⟩ := hfix
  have h1 := Equiv.Perm.eq_one_of_sign_eq_one_of_exists_fixed_fin_three (e.permCongr π) hs
    ⟨e x, by simp [Equiv.permCongr_apply, hx]⟩
  ext y
  have := Equiv.ext_iff.mp h1 (e y)
  simpa [Equiv.permCongr_apply] using this

namespace Subgroup p2m_export "Subgroup" "one mem_bot index_ker card_top zpowers ext Normal mem_zpowers index_dvd_of_le mem_map zpow_mem_zpowers index mul_mem_iff_of_index_two card_mul_index map commutator mem_zpowers_iff mk" end Subgroup
p2m_open_scoped "Subgroup" in

theorem Subgroup.forall_ncard_orbit_zpowers_ne_two_iff_mem_of_index {G : Type} [Group G] [Finite G]
    (P N : Subgroup G) (hP : P.index = 3) (hN : N.index = 2)
    (huniv : ∀ (M : Type) [CommGroup M] (f : G →* M), N ≤ f.ker) (τ : G) :
    (∀ g : G, (MulAction.orbit (Subgroup.zpowers τ) ((g : G) : G ⧸ P)).ncard ≠ 2) ↔ τ ∈ N := by
  classical
  haveI : Fintype (G ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (G ⧸ P) = 3 := by rw [← Nat.card_eq_fintype_card, ← Subgroup.index, hP]
  let ρ : G →* Equiv.Perm (G ⧸ P) := MulAction.toPermHom G (G ⧸ P)
  have hρ : ∀ g (x : G ⧸ P), ρ g x = g • x := fun g x => rfl
  have hρ1 : ∀ g : G, ρ g ((1 : G) : G ⧸ P) = ((g : G) : G ⧸ P) := fun g => by
    rw [hρ, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  let s : G →* ℤˣ := Equiv.Perm.sign.comp ρ
  have hs : ∀ g, s g = Equiv.Perm.sign (ρ g) := fun g => rfl

  have hsN : ∀ n ∈ N, s n = 1 := fun n hn => huniv ℤˣ s hn

  have hs1 : ∃ g, s g ≠ 1 := by
    by_contra hall
    push Not at hall
    have hker : ρ.ker = P := by
      ext g
      rw [MonoidHom.mem_ker]
      constructor
      · intro h
        have h1 : ((g : G) : G ⧸ P) = ((1 : G) : G ⧸ P) := by rw [← hρ1 g, h]; rfl
        rw [QuotientGroup.eq, mul_one, inv_mem_iff] at h1
        exact h1
      · intro hg
        apply Equiv.Perm.eq_one_of_sign_eq_one_of_exists_fixed_of_card_eq_three hcard (ρ g) (hall g)
        refine ⟨((1 : G) : G ⧸ P), ?_⟩
        rw [hρ1, QuotientGroup.eq, mul_one, inv_mem_iff]
        exact hg
    haveI : P.Normal := by rw [← hker]; exact MonoidHom.normal_ker ρ
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : IsCyclic (G ⧸ P) := isCyclic_of_prime_card (p := 3) (by rw [Nat.card_eq_fintype_card, hcard])
    letI : CommGroup (G ⧸ P) := IsCyclic.commGroup
    have hNP : N ≤ P := by
      have h := huniv (G ⧸ P) (QuotientGroup.mk' P)
      rwa [QuotientGroup.ker_mk'] at h
    have hdvd : P.index ∣ N.index := Subgroup.index_dvd_of_le hNP
    rw [hP, hN] at hdvd
    omega

  have hout : ∀ g, g ∉ N → s g = -1 := by
    intro g hg
    rcases Int.units_eq_one_or (s g) with h | h
    · exfalso
      obtain ⟨g₀, hg₀⟩ := hs1
      apply hg₀
      by_cases hg₀N : g₀ ∈ N
      · exact hsN g₀ hg₀N
      · have hmem : g₀ * g ∈ N := (Subgroup.mul_mem_iff_of_index_two hN).mpr (iff_of_false hg₀N hg)
        have := hsN _ hmem
        rwa [map_mul, h, mul_one] at this
    · exact h
  have hiff : s τ = -1 ↔ τ ∉ N := by
    constructor
    · intro h hτ
      rw [hsN τ hτ] at h
      exact absurd h (by decide)
    · exact hout τ

  have horb : (∀ g : G, (MulAction.orbit (Subgroup.zpowers τ) ((g : G) : G ⧸ P)).ncard ≠ 2) ↔
      ¬ ∃ x : G ⧸ P, ρ τ x ≠ x ∧ ρ τ (ρ τ x) = x := by
    constructor
    · rintro h ⟨x, hx1, hx2⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      exact h g ((MulAction.ncard_orbit_zpowers_eq_two_iff τ ((g : G) : G ⧸ P)).mpr ⟨hx1, hx2⟩)
    · intro h g hg
      have hg' := (MulAction.ncard_orbit_zpowers_eq_two_iff τ ((g : G) : G ⧸ P)).mp hg
      exact h ⟨(g : G ⧸ P), hg'.1, hg'.2⟩
  rw [horb, ← Equiv.Perm.sign_eq_neg_one_iff_exists_period_two_of_card_eq_three hcard, ← hs, hiff, not_not]

open FLT.ExplicitLift LanglandsTunnell.Lift48 in
section
open FLT.ExplicitLift LanglandsTunnell.Lift48

namespace DetUnivF3

abbrev M3 : Type := Matrix (Fin 2) (Fin 2) (ZMod 3)

def ev3 : List (Fin 2) → M3
  | [] => 1
  | 0 :: w => sbar * ev3 w
  | 1 :: w => tbar * ev3 w

def K48F3 : List M3 := [
  !![1, 0; 0, 1],
  !![2, 1; 2, 0],
  !![1, 2; 1, 1],
  !![0, 2; 1, 2],
  !![0, 2; 2, 1],
  !![0, 1; 1, 1],
  !![0, 1; 2, 0],
  !![2, 2; 0, 1],
  !![1, 0; 0, 2],
  !![2, 2; 0, 2],
  !![2, 0; 1, 1],
  !![1, 1; 2, 0],
  !![2, 0; 1, 2],
  !![1, 1; 2, 1],
  !![2, 2; 2, 0],
  !![1, 0; 1, 1],
  !![2, 1; 1, 0],
  !![1, 2; 2, 2],
  !![2, 2; 1, 0],
  !![1, 0; 2, 2],
  !![1, 1; 1, 2],
  !![2, 0; 2, 1],
  !![1, 2; 0, 1],
  !![2, 1; 0, 1],
  !![1, 1; 0, 2],
  !![2, 0; 0, 2],
  !![2, 2; 1, 2],
  !![1, 0; 2, 1],
  !![2, 1; 1, 1],
  !![1, 2; 2, 0],
  !![0, 1; 2, 2],
  !![0, 1; 1, 0],
  !![2, 2; 2, 1],
  !![1, 0; 1, 2],
  !![2, 1; 2, 2],
  !![1, 1; 0, 1],
  !![2, 0; 0, 1],
  !![1, 2; 0, 2],
  !![2, 1; 0, 2],
  !![0, 2; 2, 0],
  !![0, 2; 1, 1],
  !![1, 1; 1, 0],
  !![2, 0; 2, 2],
  !![1, 2; 1, 0],
  !![0, 1; 1, 2],
  !![0, 2; 2, 2],
  !![0, 2; 1, 0],
  !![0, 1; 2, 1]]

theorem K48F3_eq_map_ev3 : K48F3 = W48.map ev3 := by decide

theorem mem_K48F3_of_det_ne_zero : ∀ A : M3, A.det ≠ 0 → A ∈ K48F3 := by decide

theorem det_sbar : sbar.det = 1 := by decide
theorem det_tbar : tbar.det = -1 := by decide
theorem det_ev3 (w : List (Fin 2)) : (ev3 w).det = (-1) ^ (w.count 1) := by
  induction w with
  | nil => simp [ev3]
  | cons a w ih =>
    match a with
    | 0 => rw [show ev3 (0 :: w) = sbar * ev3 w from rfl, Matrix.det_mul, det_sbar, one_mul, ih, List.count_cons_of_ne (by decide)]
    | 1 => rw [show ev3 (1 :: w) = tbar * ev3 w from rfl, Matrix.det_mul, det_tbar, ih, List.count_cons_self, pow_succ, mul_comm]

def sU : GL (Fin 2) (ZMod 3) := ⟨sbar, sbar * sbar, by decide, by decide⟩
def tU : GL (Fin 2) (ZMod 3) := ⟨tbar, tbar ^ 7, by decide, by decide⟩

def evU : List (Fin 2) → GL (Fin 2) (ZMod 3)
  | [] => 1
  | 0 :: w => sU * evU w
  | 1 :: w => tU * evU w

theorem coe_evU (w : List (Fin 2)) : ((evU w : GL (Fin 2) (ZMod 3)) : M3) = ev3 w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    match a with
    | 0 => show sbar * ((evU w : GL (Fin 2) (ZMod 3)) : M3) = sbar * ev3 w; rw [ih]
    | 1 => show tbar * ((evU w : GL (Fin 2) (ZMod 3)) : M3) = tbar * ev3 w; rw [ih]

theorem sU_comm_witness : sU * sU * (tU * sU * tU * tU) = tU * sU * tU * tU * sU := by decide

theorem tU_sq_comm_witness : tU * tU * (sU * tU * tU) * sU = sU * (sU * tU * tU) := by decide

variable {M : Type*} [CommGroup M]

theorem hom_sU_eq_one (φ : GL (Fin 2) (ZMod 3) →* M) : φ sU = 1 := by
  have h' := congrArg φ sU_comm_witness
  simp only [map_mul] at h'
  have e : φ sU * (φ sU * φ sU * (φ tU * φ tU * φ tU)) = 1 * (φ sU * φ sU * (φ tU * φ tU * φ tU)) := by
    calc φ sU * (φ sU * φ sU * (φ tU * φ tU * φ tU))
          = φ sU * φ sU * (φ tU * φ sU * φ tU * φ tU) := by ac_rfl
      _ = φ tU * φ sU * φ tU * φ tU * φ sU := h'
      _ = 1 * (φ sU * φ sU * (φ tU * φ tU * φ tU)) := by rw [one_mul]; ac_rfl
  exact mul_right_cancel e

theorem hom_tU_sq_eq_one (φ : GL (Fin 2) (ZMod 3) →* M) : φ tU * φ tU = 1 := by
  have h' := congrArg φ tU_sq_comm_witness
  simp only [map_mul] at h'
  have e : φ tU * φ tU * (φ sU * φ sU * (φ tU * φ tU)) = 1 * (φ sU * φ sU * (φ tU * φ tU)) := by
    calc φ tU * φ tU * (φ sU * φ sU * (φ tU * φ tU))
          = φ tU * φ tU * (φ sU * φ tU * φ tU) * φ sU := by ac_rfl
      _ = φ sU * (φ sU * φ tU * φ tU) := h'
      _ = 1 * (φ sU * φ sU * (φ tU * φ tU)) := by rw [one_mul]; ac_rfl
  exact mul_right_cancel e

theorem hom_evU (φ : GL (Fin 2) (ZMod 3) →* M) (w : List (Fin 2)) : φ (evU w) = φ tU ^ (w.count 1) := by
  induction w with
  | nil => simp [evU]
  | cons a w ih =>
    match a with
    | 0 => rw [show evU (0 :: w) = sU * evU w from rfl, map_mul, hom_sU_eq_one, one_mul, ih, List.count_cons_of_ne (by decide)]
    | 1 => rw [show evU (1 :: w) = tU * evU w from rfl, map_mul, ih, List.count_cons_self, pow_succ, mul_comm]

theorem hom_eq_one_of_det_eq_one (φ : GL (Fin 2) (ZMod 3) →* M) (g : GL (Fin 2) (ZMod 3))
    (hg : ((g : GL (Fin 2) (ZMod 3)) : M3).det = 1) : φ g = 1 := by
  have hmem := mem_K48F3_of_det_ne_zero (g : M3) (by rw [hg]; decide)
  rw [K48F3_eq_map_ev3, List.mem_map] at hmem
  obtain ⟨w, -, hw⟩ := hmem
  have hgw : g = evU w := Units.ext (by rw [coe_evU, hw])
  rw [hgw, hom_evU]

  have hdet : ((-1 : ZMod 3)) ^ (w.count 1) = 1 := by rw [← det_ev3, hw, hg]
  rcases Nat.even_or_odd (w.count 1) with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk, ← two_mul, pow_mul, sq, hom_tU_sq_eq_one, one_pow]
  · exfalso
    rw [hk, pow_succ, pow_mul] at hdet
    have : ((-1 : ZMod 3)) ^ 2 = 1 := by decide
    rw [this, one_pow, one_mul] at hdet
    exact absurd hdet (by decide)

end DetUnivF3

namespace LanglandsTunnell p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff detKer_normal sylowH Lift48.W48 Lift48.evalWord card_sylowH P2.Artin.exists_ne_bot_forall_inertia_ne_bot_dvd" end LanglandsTunnell
p2m_open_scoped "LanglandsTunnell" in
open DetUnivF3 in

theorem LanglandsTunnell.detKer_le_ker {L : Type} [Field L] [NumberField L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (M : Type) [CommGroup M] (f : (L ≃ₐ[ℚ] L) →* M) : detKer e ≤ f.ker := by
  intro γ hγ
  rw [MonoidHom.mem_ker]
  rw [mem_detKer_iff] at hγ
  have h := hom_eq_one_of_det_eq_one (f.comp e.symm.toMonoidHom) (e γ) hγ
  simpa using h

end

section Indices
variable {L : Type} [Field L] [NumberField L]

theorem card_GL2_F3 : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
  rw [Matrix.card_GL_field]
  simp [ZMod.card, Fin.prod_univ_two]

p2m_open_scoped "LanglandsTunnell" in

theorem LanglandsTunnell.index_sylowH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    (sylowH e).index = 3 := by
  have h1 := Subgroup.card_mul_index (sylowH e)
  rw [card_sylowH, Nat.card_congr e.toEquiv, card_GL2_F3] at h1
  omega

p2m_open_scoped "LanglandsTunnell" in

theorem LanglandsTunnell.index_detKer (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    (detKer e).index = 2 := by
  unfold detKer
  rw [Subgroup.index_ker]
  have hr : (Matrix.GeneralLinearGroup.det.comp e.toMonoidHom).range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro u
    have hu : u = 1 ∨ u = -1 := by fin_cases u <;> decide
    rcases hu with rfl | rfl
    · exact ⟨1, by simp⟩
    · refine ⟨e.symm DetUnivF3.tU, ?_⟩
      have htU : Matrix.GeneralLinearGroup.det DetUnivF3.tU = -1 := by decide
      simp [htU]
  rw [hr, Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  decide

p2m_open_scoped "LanglandsTunnell" in

theorem LanglandsTunnell.finrank_fixFld_sylowH [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Module.finrank ℚ ↥(fixFld (sylowH e)) = 3 := by
  have h16 : Module.finrank ↥(fixFld (sylowH e)) L = 16 := by
    rw [show fixFld (sylowH e) = IntermediateField.fixedField (sylowH e) from rfl,
      IntermediateField.finrank_fixedField_eq_card, card_sylowH]
  have h48 : Module.finrank ℚ L = 48 := by
    rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr e.toEquiv, card_GL2_F3]
  have htower := Module.finrank_mul_finrank ℚ ↥(fixFld (sylowH e)) L
  rw [h16, h48] at htower
  omega

end Indices

p2m_open_scoped "LanglandsTunnell" in

theorem LanglandsTunnell.forall_ncard_orbit_sylowH_ne_two_iff_mem_detKer {L : Type} [Field L] [NumberField L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (τ : L ≃ₐ[ℚ] L) :
    (∀ g : L ≃ₐ[ℚ] L, (MulAction.orbit (Subgroup.zpowers τ) ((g : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ sylowH e)).ncard ≠ 2) ↔
      τ ∈ detKer e := by
  haveI : Finite (L ≃ₐ[ℚ] L) := Finite.of_equiv _ e.toEquiv.symm
  exact Subgroup.forall_ncard_orbit_zpowers_ne_two_iff_mem_of_index (sylowH e) (detKer e)
    (index_sylowH e) (index_detKer e) (detKer_le_ker e) τ

section L13
open scoped Pointwise
variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]

theorem HOLE_FROB (v : HeightOneSpectrum (𝓞 ℚ))
    (hunr : ∀ Q : Ideal (𝓞 L), Q.IsMaximal → Q.under (𝓞 ℚ) = v.asIdeal → Q.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    ∃ (Q₀ : Ideal (𝓞 L)) (σ₀ : L ≃ₐ[ℚ] L), Q₀.IsMaximal ∧ Q₀.under (𝓞 ℚ) = v.asIdeal ∧ IsArithFrobAt (𝓞 ℚ) σ₀ Q₀ ∧
      ∀ (Q : Ideal (𝓞 L)) (σ : L ≃ₐ[ℚ] L), Q.IsMaximal → Q.under (𝓞 ℚ) = v.asIdeal → IsArithFrobAt (𝓞 ℚ) σ Q →
        ∃ g : L ≃ₐ[ℚ] L, σ = g * σ₀ * g⁻¹ := by
  classical
  haveI := v.isMaximal

  have hker : RingHom.ker (algebraMap (𝓞 ℚ) (𝓞 L)) ≤ v.asIdeal := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have h0 : x = 0 := FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 L) (by rw [hx, map_zero])
    rw [h0]; exact zero_mem _
  obtain ⟨Q₀, hQ₀max, hQ₀v⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) v.asIdeal hker
  have hQ₀v' : Q₀.under (𝓞 ℚ) = v.asIdeal := hQ₀v
  have hQ₀bot : Q₀ ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [← hQ₀v', h, Ideal.under_def, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 L))]
  haveI := hQ₀max
  haveI : Finite (𝓞 L ⧸ Q₀) := Ideal.finiteQuotientOfFreeOfNeBot Q₀ hQ₀bot
  obtain ⟨σ₀, hσ₀⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 ℚ) (L ≃ₐ[ℚ] L) Q₀
  refine ⟨Q₀, σ₀, hQ₀max, hQ₀v', hσ₀, fun Q σ hQ hQv hσ => ?_⟩
  haveI := hQ
  obtain ⟨g, rfl⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 ℚ) (𝓞 L) (L ≃ₐ[ℚ] L) Q₀ Q (hQ₀v'.trans hQv.symm)
  have h1 := hσ₀.conj g
  have h2 := hσ.mul_inv_mem_inertia h1
  rw [hunr _ hQ hQv, Subgroup.mem_bot] at h2
  exact ⟨g, by rw [← mul_inv_eq_one, h2]⟩

theorem orbit_zpowers_quotient_ncard_eq_one_iff (N : Subgroup (L ≃ₐ[ℚ] L)) [N.Normal] (τ g : L ≃ₐ[ℚ] L) :
    (MulAction.orbit (Subgroup.zpowers τ) ((g : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ N)).ncard = 1 ↔ τ ∈ N := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h
    have hg : ((g : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ N) ∈ MulAction.orbit (Subgroup.zpowers τ) ((g : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ N) :=
      MulAction.mem_orbit_self _
    have hτg : (⟨τ, Subgroup.mem_zpowers τ⟩ : Subgroup.zpowers τ) • ((g : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ N) ∈
        MulAction.orbit (Subgroup.zpowers τ) ((g : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ N) := MulAction.mem_orbit _ _
    rw [ha, Set.mem_singleton_iff] at hg hτg
    rw [← hg] at hτg
    change τ • ((g : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ N) = _ at hτg
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at hτg

    have h2 := ‹N.Normal›.conj_mem _ hτg g
    have h3 : g * ((τ * g)⁻¹ * g) * g⁻¹ = τ⁻¹ := by group
    rw [h3] at h2
    simpa using N.inv_mem h2
  · intro hτ
    rw [Set.ncard_eq_one]
    refine ⟨((g : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ N), ?_⟩
    ext x
    rw [Set.mem_singleton_iff, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨⟨s, hs⟩, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      change (τ ^ k) • ((g : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ N) = _
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      have hk : (τ ^ k)⁻¹ ∈ N := N.inv_mem (N.zpow_mem hτ k)
      have h2 := ‹N.Normal›.conj_mem _ hk g⁻¹
      have h3 : g⁻¹ * (τ ^ k)⁻¹ * g⁻¹⁻¹ = (τ ^ k * g)⁻¹ * g := by group
      rwa [h3] at h2
    · rintro rfl
      exact ⟨1, one_smul _ _⟩

end L13

namespace C3L2

theorem card_le_of_forall_pow_eq (F : Type*) [Field F] [Fintype F] {m : ℕ} (hm : 1 < m) (h : ∀ a : F, a ^ m = a) :
    Fintype.card F ≤ m := by
  classical
  have hp := FiniteField.X_pow_card_sub_X_ne_zero F hm
  calc Fintype.card F = (Finset.univ : Finset F).val.card := rfl
    _ ≤ (Polynomial.X ^ m - Polynomial.X : Polynomial F).roots.card := by
        apply Multiset.card_le_card
        rw [Multiset.le_iff_subset Finset.univ.nodup]
        intro a _
        rw [Polynomial.mem_roots hp]
        simp [h a]
    _ ≤ (Polynomial.X ^ m - Polynomial.X : Polynomial F).natDegree := Polynomial.card_roots' _
    _ = m := FiniteField.X_pow_card_sub_X_natDegree_eq F hm

theorem ncard_orbit_zpowers_conj {G α : Type*} [Group G] [MulAction G α] (σ a : G) (x : α) :
    (MulAction.orbit (Subgroup.zpowers (a * σ * a⁻¹)) (a • x)).ncard = (MulAction.orbit (Subgroup.zpowers σ) x).ncard := by
  have himage : MulAction.orbit (Subgroup.zpowers (a * σ * a⁻¹)) (a • x) =
      (fun y => a • y) '' MulAction.orbit (Subgroup.zpowers σ) x := by
    ext y
    simp only [MulAction.mem_orbit_iff, Set.mem_image]
    constructor
    · rintro ⟨⟨s, hs⟩, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      refine ⟨σ ^ k • x, ⟨⟨σ ^ k, Subgroup.zpow_mem_zpowers σ k⟩, rfl⟩, ?_⟩
      change a • σ ^ k • x = (a * σ * a⁻¹) ^ k • a • x
      rw [conj_zpow, mul_smul, mul_smul, inv_smul_smul]
    · rintro ⟨z, ⟨⟨s, hs⟩, rfl⟩, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      refine ⟨⟨(a * σ * a⁻¹) ^ k, Subgroup.zpow_mem_zpowers _ k⟩, ?_⟩
      change (a * σ * a⁻¹) ^ k • a • x = a • σ ^ k • x
      rw [conj_zpow, mul_smul, mul_smul, inv_smul_smul]
  rw [himage, Set.ncard_image_of_injective _ (MulAction.injective a)]

theorem ncard_orbit_zpowers_one_eq_minimalPeriod {G : Type*} [Group G] [Finite G] (H : Subgroup G) (σ : G) :
    (MulAction.orbit (Subgroup.zpowers σ) ((1 : G) : G ⧸ H)).ncard =
      Function.minimalPeriod (fun x : G ⧸ H => σ • x) ((1 : G) : G ⧸ H) := by
  classical
  haveI : Fintype (MulAction.orbit (Subgroup.zpowers σ) ((1 : G) : G ⧸ H)) := Fintype.ofFinite _
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  first
    | exact (MulAction.minimalPeriod_eq_card σ ((1 : G) : G ⧸ H)).symm
    | (convert (MulAction.minimalPeriod_eq_card σ ((1 : G) : G ⧸ H)).symm using 2 <;>
        first | rfl | exact Subsingleton.elim _ _ | exact Fintype.ofFinite _)

theorem isPeriodicPt_smul_one_iff {G : Type*} [Group G] (H : Subgroup G) (σ : G) (n : ℕ) :
    Function.IsPeriodicPt (fun x : G ⧸ H => σ • x) n ((1 : G) : G ⧸ H) ↔ σ ^ n ∈ H := by
  rw [Function.IsPeriodicPt, Function.IsFixedPt, smul_iterate]
  change σ ^ n • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) ↔ _
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L] (H : Subgroup (L ≃ₐ[ℚ] L))

omit [IsGalois ℚ L] in
theorem restrictScalars_mem (h : L ≃ₐ[↥(fixFld H)] L) : AlgEquiv.restrictScalars ℚ h ∈ H := by
  have hmem : AlgEquiv.restrictScalars ℚ h ∈ (IntermediateField.fixedField H).fixingSubgroup :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx => h.commutes ⟨x, hx⟩
  rwa [IntermediateField.fixingSubgroup_fixedField] at hmem

omit [IsGalois ℚ L] in

theorem smul_algebraMap_of_mem {τ : L ≃ₐ[ℚ] L} (hτ : τ ∈ H) (x : 𝓞 ↥(fixFld H)) :
    τ • (algebraMap (𝓞 ↥(fixFld H)) (𝓞 L) x) = algebraMap (𝓞 ↥(fixFld H)) (𝓞 L) x := by
  apply RingOfIntegers.ext
  change τ (((x : ↥(fixFld H)) : L)) = ((x : ↥(fixFld H)) : L)
  have hτ' : τ ∈ (IntermediateField.fixedField H).fixingSubgroup := by
    rwa [IntermediateField.fixingSubgroup_fixedField]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ' _ (x : ↥(fixFld H)).2

theorem mk_pow_smul {σ : L ≃ₐ[ℚ] L} {Q : Ideal (𝓞 L)} (hσ : IsArithFrobAt (𝓞 ℚ) σ Q) (n : ℕ) (x : 𝓞 L) :
    Ideal.Quotient.mk Q ((σ ^ n) • x) = Ideal.Quotient.mk Q x ^ (Nat.card (𝓞 ℚ ⧸ Q.under (𝓞 ℚ)) ^ n) := by
  have h1 : ∀ y : 𝓞 L, Ideal.Quotient.mk Q (σ • y) = Ideal.Quotient.mk Q y ^ Nat.card (𝓞 ℚ ⧸ Q.under (𝓞 ℚ)) := by
    intro y
    rw [← map_pow, Ideal.Quotient.eq]
    exact hσ y
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, ih (σ • x), h1, ← pow_mul, ← pow_succ']

omit [IsGalois ℚ L] in

theorem natCard_quotient_eq_pow (v : HeightOneSpectrum (𝓞 ℚ)) (𝔓 : HeightOneSpectrum (𝓞 ↥(fixFld H)))
    (h𝔓 : 𝔓.asIdeal.under (𝓞 ℚ) = v.asIdeal) :
    Nat.card (𝓞 ↥(fixFld H) ⧸ 𝔓.asIdeal) = Nat.card (𝓞 ℚ ⧸ v.asIdeal) ^ v.asIdeal.inertiaDeg' 𝔓.asIdeal := by
  classical
  haveI : 𝔓.asIdeal.LiesOver v.asIdeal := ⟨h𝔓.symm⟩
  haveI := v.isMaximal
  haveI := 𝔓.isMaximal
  letI : Field (𝓞 ℚ ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 ℚ ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  haveI : Finite (𝓞 ↥(fixFld H) ⧸ 𝔓.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔓.ne_bot
  haveI : Fintype (𝓞 ℚ ⧸ v.asIdeal) := Fintype.ofFinite _
  haveI : Fintype (𝓞 ↥(fixFld H) ⧸ 𝔓.asIdeal) := Fintype.ofFinite _
  rw [Ideal.inertiaDeg_algebraMap, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := 𝓞 ℚ ⧸ v.asIdeal) (V := 𝓞 ↥(fixFld H) ⧸ 𝔓.asIdeal)]

theorem pow_inertiaDeg_mem (v : HeightOneSpectrum (𝓞 ℚ)) (Q : Ideal (𝓞 L)) (hQ : Q.IsMaximal) (hQv : Q.under (𝓞 ℚ) = v.asIdeal)
    (hunrQ : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) (σ : L ≃ₐ[ℚ] L) (hσ : IsArithFrobAt (𝓞 ℚ) σ Q)
    (𝔓 : HeightOneSpectrum (𝓞 ↥(fixFld H))) (h𝔓Q : 𝔓.asIdeal = Q.under (𝓞 ↥(fixFld H))) :
    σ ^ (v.asIdeal.inertiaDeg' 𝔓.asIdeal) ∈ H := by
  classical
  haveI := hQ
  have hQbot : Q ≠ ⊥ := fun h => v.ne_bot (by
    rw [← hQv, h, Ideal.under_def, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 L))])
  haveI : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQbot

  obtain ⟨h, hh⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 ↥(fixFld H)) (L ≃ₐ[↥(fixFld H)] L) Q
  have h𝔓v : 𝔓.asIdeal.under (𝓞 ℚ) = v.asIdeal := by rw [h𝔓Q, Ideal.under_under, hQv]
  have hcard : Nat.card (𝓞 ↥(fixFld H) ⧸ Q.under (𝓞 ↥(fixFld H))) =
      Nat.card (𝓞 ℚ ⧸ Q.under (𝓞 ℚ)) ^ v.asIdeal.inertiaDeg' 𝔓.asIdeal := by
    rw [← h𝔓Q, natCard_quotient_eq_pow H v 𝔓 h𝔓v, hQv]
  set h' : L ≃ₐ[ℚ] L := AlgEquiv.restrictScalars ℚ h with hh'
  have hh'mem : h' ∈ H := restrictScalars_mem H h

  have hu : σ ^ (v.asIdeal.inertiaDeg' 𝔓.asIdeal) * h'⁻¹ ∈ Q.inertia (L ≃ₐ[ℚ] L) := by
    rw [Ideal.inertia, AddSubgroup.mem_inertia]
    intro x
    set y := h'⁻¹ • x with hy
    have hx : x = h' • y := by rw [hy, smul_inv_smul]
    rw [hx, mul_smul, inv_smul_smul]
    change σ ^ (v.asIdeal.inertiaDeg' 𝔓.asIdeal) • y - h • y ∈ Q
    rw [← Ideal.Quotient.eq, mk_pow_smul hσ, ← hcard, ← map_pow, Ideal.Quotient.eq]
    have := hh y

    simpa using Q.neg_mem (Q.sub_mem this (Q.zero_mem))
  rw [hunrQ, Subgroup.mem_bot, mul_inv_eq_one] at hu
  rw [hu]
  exact hh'mem

theorem inertiaDeg_le_of_pow_mem (v : HeightOneSpectrum (𝓞 ℚ)) (Q : Ideal (𝓞 L)) (_hQ : Q.IsMaximal) (hQv : Q.under (𝓞 ℚ) = v.asIdeal)
    (σ : L ≃ₐ[ℚ] L) (hσ : IsArithFrobAt (𝓞 ℚ) σ Q)
    (𝔓 : HeightOneSpectrum (𝓞 ↥(fixFld H))) (h𝔓Q : 𝔓.asIdeal = Q.under (𝓞 ↥(fixFld H)))
    {d : ℕ} (hd : 1 ≤ d) (hmem : σ ^ d ∈ H) : v.asIdeal.inertiaDeg' 𝔓.asIdeal ≤ d := by
  classical
  haveI := v.isMaximal
  haveI := 𝔓.isMaximal
  have h𝔓v : 𝔓.asIdeal.under (𝓞 ℚ) = v.asIdeal := by rw [h𝔓Q, Ideal.under_under, hQv]
  letI : Field (𝓞 ↥(fixFld H) ⧸ 𝔓.asIdeal) := Ideal.Quotient.field 𝔓.asIdeal
  haveI : Finite (𝓞 ↥(fixFld H) ⧸ 𝔓.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔓.ne_bot
  haveI : Fintype (𝓞 ↥(fixFld H) ⧸ 𝔓.asIdeal) := Fintype.ofFinite _

  set q := Nat.card (𝓞 ℚ ⧸ v.asIdeal) with hq
  have hq2 : 1 < q := by
    letI : Field (𝓞 ℚ ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    haveI : Finite (𝓞 ℚ ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
    haveI : Fintype (𝓞 ℚ ⧸ v.asIdeal) := Fintype.ofFinite _
    rw [hq, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card

  have hall : ∀ a : 𝓞 ↥(fixFld H) ⧸ 𝔓.asIdeal, a ^ (q ^ d) = a := by
    intro a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    have key := mk_pow_smul hσ d (algebraMap (𝓞 ↥(fixFld H)) (𝓞 L) x)
    rw [smul_algebraMap_of_mem H hmem x, hQv] at key

    rw [← map_pow, eq_comm, Ideal.Quotient.eq, h𝔓Q]
    change algebraMap (𝓞 ↥(fixFld H)) (𝓞 L) (x - x ^ q ^ d) ∈ Q
    rw [map_sub, map_pow, ← Ideal.Quotient.eq, map_pow]
    exact key
  have hle := card_le_of_forall_pow_eq (𝓞 ↥(fixFld H) ⧸ 𝔓.asIdeal) (Nat.one_lt_pow (by omega) hq2) hall
  rw [← Nat.card_eq_fintype_card, natCard_quotient_eq_pow H v 𝔓 h𝔓v] at hle
  exact (Nat.pow_le_pow_iff_right hq2).mp hle

theorem inertiaDeg_eq_ncard_orbit_one (v : HeightOneSpectrum (𝓞 ℚ)) (Q : Ideal (𝓞 L)) (hQ : Q.IsMaximal)
    (hQv : Q.under (𝓞 ℚ) = v.asIdeal) (hunrQ : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) (σ : L ≃ₐ[ℚ] L) (hσ : IsArithFrobAt (𝓞 ℚ) σ Q)
    (𝔓 : HeightOneSpectrum (𝓞 ↥(fixFld H))) (h𝔓Q : 𝔓.asIdeal = Q.under (𝓞 ↥(fixFld H))) :
    v.asIdeal.inertiaDeg' 𝔓.asIdeal = (MulAction.orbit (Subgroup.zpowers σ) ((1 : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ H)).ncard := by
  classical
  haveI : Finite (L ≃ₐ[ℚ] L) := inferInstance
  rw [ncard_orbit_zpowers_one_eq_minimalPeriod]
  set f := v.asIdeal.inertiaDeg' 𝔓.asIdeal with hf
  set d := Function.minimalPeriod (fun x : (L ≃ₐ[ℚ] L) ⧸ H => σ • x) ((1 : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ H) with hd

  have hP1 : Function.IsPeriodicPt (fun x : (L ≃ₐ[ℚ] L) ⧸ H => σ • x) f ((1 : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ H) :=
    (isPeriodicPt_smul_one_iff H σ f).mpr (pow_inertiaDeg_mem H v Q hQ hQv hunrQ σ hσ 𝔓 h𝔓Q)
  have hfpos : 0 < f := by
    haveI := v.isMaximal
    haveI : 𝔓.asIdeal.LiesOver v.asIdeal := ⟨by rw [h𝔓Q, Ideal.under_under, hQv]⟩
    exact Ideal.inertiaDeg'_pos v.asIdeal 𝔓.asIdeal
  have hdvd : d ∣ f := hP1.minimalPeriod_dvd
  have hdpos : 0 < d := hP1.minimalPeriod_pos hfpos

  have hP2 : σ ^ d ∈ H := (isPeriodicPt_smul_one_iff H σ d).mp (Function.isPeriodicPt_minimalPeriod _ _)
  have hle : f ≤ d := inertiaDeg_le_of_pow_mem H v Q hQ hQv σ hσ 𝔓 h𝔓Q hdpos hP2
  exact le_antisymm hle (Nat.le_of_dvd hfpos hdvd)

theorem HOLE_ORBIT (v : HeightOneSpectrum (𝓞 ℚ))
    (hunr : ∀ Q : Ideal (𝓞 L), Q.IsMaximal → Q.under (𝓞 ℚ) = v.asIdeal → Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (Q₀ : Ideal (𝓞 L)) (σ₀ : L ≃ₐ[ℚ] L) (hQ₀ : Q₀.IsMaximal) (hQ₀v : Q₀.under (𝓞 ℚ) = v.asIdeal)
    (hσ₀ : IsArithFrobAt (𝓞 ℚ) σ₀ Q₀) :
    (∀ 𝔓 : HeightOneSpectrum (𝓞 ↥(fixFld H)), 𝔓.under (𝓞 ℚ) = v →
        ∃ g : L ≃ₐ[ℚ] L, (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal =
          (MulAction.orbit (Subgroup.zpowers σ₀) ((g : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ H)).ncard) ∧
    (∀ g : L ≃ₐ[ℚ] L, ∃ 𝔓 : HeightOneSpectrum (𝓞 ↥(fixFld H)), 𝔓.under (𝓞 ℚ) = v ∧
        (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal =
          (MulAction.orbit (Subgroup.zpowers σ₀) ((g : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ H)).ncard) := by
  classical
  haveI := hQ₀
  constructor
  · intro 𝔓 h𝔓v
    haveI := 𝔓.isMaximal

    have hker : RingHom.ker (algebraMap (𝓞 ↥(fixFld H)) (𝓞 L)) ≤ 𝔓.asIdeal := by
      intro x hx
      rw [RingHom.mem_ker] at hx
      have h0 : x = 0 := FaithfulSMul.algebraMap_injective (𝓞 ↥(fixFld H)) (𝓞 L) (by rw [hx, map_zero])
      rw [h0]; exact zero_mem _
    obtain ⟨Q, hQmax, hQ𝔓⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) 𝔓.asIdeal hker
    have hQ𝔓' : Q.under (𝓞 ↥(fixFld H)) = 𝔓.asIdeal := hQ𝔓
    have hQv : Q.under (𝓞 ℚ) = v.asIdeal := by
      rw [← Ideal.under_under (B := 𝓞 ↥(fixFld H)), hQ𝔓', ← h𝔓v]; rfl
    haveI := hQmax
    obtain ⟨g, rfl⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 ℚ) (𝓞 L) (L ≃ₐ[ℚ] L) Q₀ Q (hQ₀v.trans hQv.symm)
    have hσ : IsArithFrobAt (𝓞 ℚ) (g * σ₀ * g⁻¹) (g • Q₀) := hσ₀.conj g
    refine ⟨g⁻¹, ?_⟩
    have h1 := inertiaDeg_eq_ncard_orbit_one H v (g • Q₀) hQmax hQv (hunr _ hQmax hQv) _ hσ 𝔓 hQ𝔓'.symm
    rw [show (𝔓.under (𝓞 ℚ)).asIdeal = v.asIdeal from congrArg HeightOneSpectrum.asIdeal h𝔓v, h1]
    have h2 := ncard_orbit_zpowers_conj σ₀ g ((g⁻¹ : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ H)
    have h3 : g • ((g⁻¹ : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ H) = ((1 : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ H) := by
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_inv_cancel]
    rw [h3] at h2
    exact h2
  · intro g
    set Q : Ideal (𝓞 L) := g⁻¹ • Q₀ with hQdef
    haveI : Q.IsPrime := Ideal.IsPrime.smul g⁻¹
    have hQv : Q.under (𝓞 ℚ) = v.asIdeal := by rw [hQdef, Ideal.under_smul, hQ₀v]
    have hQbot : Q ≠ ⊥ := fun h => v.ne_bot (by
      rw [← hQv, h, Ideal.under_def, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 L))])
    have hQmax : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQbot
    haveI := hQmax
    have hσ : IsArithFrobAt (𝓞 ℚ) (g⁻¹ * σ₀ * g⁻¹⁻¹) Q := hσ₀.conj g⁻¹

    have hPmax : (Q.under (𝓞 ↥(fixFld H))).IsMaximal := Ideal.IsMaximal.under _ Q
    have hPbot : Q.under (𝓞 ↥(fixFld H)) ≠ ⊥ := fun h => v.ne_bot (by
      rw [← hQv, ← Ideal.under_under (B := 𝓞 ↥(fixFld H)), h, Ideal.under_def,
        Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 ↥(fixFld H)))])
    let 𝔓 : HeightOneSpectrum (𝓞 ↥(fixFld H)) := ⟨Q.under (𝓞 ↥(fixFld H)), hPmax.isPrime, hPbot⟩
    have h𝔓v : 𝔓.under (𝓞 ℚ) = v := by
      apply HeightOneSpectrum.ext
      change (Q.under (𝓞 ↥(fixFld H))).under (𝓞 ℚ) = v.asIdeal
      rw [Ideal.under_under, hQv]
    refine ⟨𝔓, h𝔓v, ?_⟩
    have h1 := inertiaDeg_eq_ncard_orbit_one H v Q hQmax hQv (hunr _ hQmax hQv) _ hσ 𝔓 rfl
    rw [show (𝔓.under (𝓞 ℚ)).asIdeal = v.asIdeal from congrArg HeightOneSpectrum.asIdeal h𝔓v, h1]
    have h2 := ncard_orbit_zpowers_conj σ₀ g⁻¹ ((g : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ H)
    have h3 : g⁻¹ • ((g : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ H) = ((1 : L ≃ₐ[ℚ] L) : (L ≃ₐ[ℚ] L) ⧸ H) := by
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]
    rw [h3] at h2
    exact h2

end C3L2

theorem solution
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    ∃ (S₀ : Finset (HeightOneSpectrum (𝓞 ℚ))) (χ : HeightOneSpectrum (𝓞 ℚ) → ℂ),
      (∀ v ∉ S₀, ∀ (Q : Ideal (𝓞 L)) (σ : L ≃ₐ[ℚ] L), Q.IsMaximal → Q.under (𝓞 ℚ) = v.asIdeal →
          IsArithFrobAt (𝓞 ℚ) σ Q → (χ v = 1 ↔ σ ∈ detKer e) ∧ (χ v = -1 ↔ σ ∉ detKer e)) ∧
      (∀ v ∉ S₀, χ v * χ v = 1) ∧
      (∀ v ∉ S₀, (χ v = 1 ↔ ∃ 𝔓 : HeightOneSpectrum (𝓞 ↥(fixFld (detKer e))),
          𝔓.under (𝓞 ℚ) = v ∧ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal = 1)) ∧
      (∀ v ∉ S₀, (χ v = 1 ↔ ∀ 𝔓 : HeightOneSpectrum (𝓞 ↥(fixFld (sylowH e))), 𝔓.under (𝓞 ℚ) = v →
          (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal ≠ 2)) ∧
      (∀ v ∉ S₀, ∀ Q : Ideal (𝓞 L), Q.IsMaximal → Q.under (𝓞 ℚ) = v.asIdeal → Q.inertia (L ≃ₐ[ℚ] L) = ⊥) := by
  classical

  obtain ⟨𝔯, h𝔯0, h𝔯⟩ := LanglandsTunnell.P2.Artin.exists_ne_bot_forall_inertia_ne_bot_dvd ℚ L
  have h𝔯0' : 𝔯 ≠ 0 := by rwa [Ne, Submodule.zero_eq_bot]
  set S₀ : Finset (HeightOneSpectrum (𝓞 ℚ)) := (Ideal.finite_factors h𝔯0').toFinset with hS₀
  have hunr : ∀ v ∉ S₀, ∀ Q : Ideal (𝓞 L), Q.IsMaximal → Q.under (𝓞 ℚ) = v.asIdeal → Q.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
    intro v hv Q hQ hQv
    by_contra hne
    exact hv ((Set.Finite.mem_toFinset _).mpr (h𝔯 v Q hQ hQv hne))

  have hfrob : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ (Q₀ : Ideal (𝓞 L)) (σ₀ : L ≃ₐ[ℚ] L), v ∉ S₀ →
      Q₀.IsMaximal ∧ Q₀.under (𝓞 ℚ) = v.asIdeal ∧ IsArithFrobAt (𝓞 ℚ) σ₀ Q₀ ∧
      ∀ (Q : Ideal (𝓞 L)) (σ : L ≃ₐ[ℚ] L), Q.IsMaximal → Q.under (𝓞 ℚ) = v.asIdeal → IsArithFrobAt (𝓞 ℚ) σ Q →
        ∃ g : L ≃ₐ[ℚ] L, σ = g * σ₀ * g⁻¹ := by
    intro v
    by_cases hv : v ∈ S₀
    · exact ⟨⊥, 1, fun h => absurd hv h⟩
    · obtain ⟨Q₀, σ₀, h⟩ := HOLE_FROB v (hunr v hv)
      exact ⟨Q₀, σ₀, fun _ => h⟩
  choose Q₀ σ₀ hQσ using hfrob

  have h1ne : (1 : ℂ) ≠ -1 := by norm_num
  have hχiff : ∀ v, ((if σ₀ v ∈ detKer e then (1 : ℂ) else -1) = 1 ↔ σ₀ v ∈ detKer e) := by
    intro v; by_cases h : σ₀ v ∈ detKer e <;> simp [h, h1ne.symm]
  have hχiff' : ∀ v, ((if σ₀ v ∈ detKer e then (1 : ℂ) else -1) = -1 ↔ σ₀ v ∉ detKer e) := by
    intro v; by_cases h : σ₀ v ∈ detKer e <;> simp [h, h1ne]
  refine ⟨S₀, fun v => if σ₀ v ∈ detKer e then 1 else -1, ?_, ?_, ?_, ?_, hunr⟩
  ·
    intro v hv Q σ hQ hQv hσ
    obtain ⟨hQ₀, hQ₀v, hσ₀, hconj⟩ := hQσ v hv
    obtain ⟨g, rfl⟩ := hconj Q σ hQ hQv hσ
    have hiff : g * σ₀ v * g⁻¹ ∈ detKer e ↔ σ₀ v ∈ detKer e :=
      ⟨fun h => by simpa [mul_assoc] using (detKer_normal e).conj_mem _ h g⁻¹, fun h => (detKer_normal e).conj_mem _ h g⟩
    rw [hiff]
    exact ⟨hχiff v, hχiff' v⟩
  ·
    intro v hv
    show (if σ₀ v ∈ detKer e then (1 : ℂ) else -1) * (if σ₀ v ∈ detKer e then (1 : ℂ) else -1) = 1
    by_cases h : σ₀ v ∈ detKer e <;> simp [h]
  ·
    intro v hv
    show (if σ₀ v ∈ detKer e then (1 : ℂ) else -1) = 1 ↔ _
    rw [hχiff]
    obtain ⟨hQ₀, hQ₀v, hσ₀, -⟩ := hQσ v hv
    obtain ⟨hdeg, hsurj⟩ := C3L2.HOLE_ORBIT (detKer e) v (hunr v hv) (Q₀ v) (σ₀ v) hQ₀ hQ₀v hσ₀
    constructor
    · intro hmem
      obtain ⟨𝔓, h𝔓v, h𝔓deg⟩ := hsurj 1
      refine ⟨𝔓, h𝔓v, ?_⟩
      rw [h𝔓deg]
      exact (orbit_zpowers_quotient_ncard_eq_one_iff (detKer e) (σ₀ v) 1).mpr hmem
    · rintro ⟨𝔓, h𝔓v, h𝔓deg⟩
      obtain ⟨g, hg⟩ := hdeg 𝔓 h𝔓v
      rw [hg] at h𝔓deg
      exact (orbit_zpowers_quotient_ncard_eq_one_iff (detKer e) (σ₀ v) g).mp h𝔓deg
  ·
    intro v hv
    show (if σ₀ v ∈ detKer e then (1 : ℂ) else -1) = 1 ↔ _
    rw [hχiff, ← LanglandsTunnell.forall_ncard_orbit_sylowH_ne_two_iff_mem_detKer e (σ₀ v)]
    obtain ⟨hQ₀, hQ₀v, hσ₀, -⟩ := hQσ v hv
    obtain ⟨hdeg, hsurj⟩ := C3L2.HOLE_ORBIT (sylowH e) v (hunr v hv) (Q₀ v) (σ₀ v) hQ₀ hQ₀v hσ₀
    constructor
    · intro h 𝔓 h𝔓v
      obtain ⟨g, hg⟩ := hdeg 𝔓 h𝔓v
      rw [hg]
      exact h g
    · intro h g
      obtain ⟨𝔓, h𝔓v, h𝔓deg⟩ := hsurj g
      rw [← h𝔓deg]
      exact h 𝔓 h𝔓v

end S_LanglandsTunnell_exists_resolventSignChar_sylowH
end P2MW
export P2MW.S_LanglandsTunnell_exists_resolventSignChar_sylowH (solution)
