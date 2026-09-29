-- Prove2me | solution 1 for Ihara.mennickeQ_le_commutator_sup_mennickeQ_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/84fbacf0-457a-581f-a058-05f3d458ef4e

import Definitions.Def_IharaMennickeCarrier
import Theorems.Thm_Ihara_mennickeLemma21
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Group
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_mennickeQ_le_commutator_sup_mennickeQ_mul

set_option Elab.async false
set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff slToAway_mennickeA_pow_mem qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ mem_mennickeZ_iff MennickeLemma21 mennickeLemma21_iff ZAway slToAway coe_slToAway zAwayToZMod zAwayToZMod_algebraMap mennickeLemma21"
p2m_open "Ihara"

open Subgroup Matrix
open scoped MatrixGroups
open scoped commutatorElement

section GateSlice

variable (q : ℕ)

theorem qInv_mul_natCast_q_sq :
    qInv q * ((q : ℕ) : ZAway q) ^ 2 = ((q : ℕ) : ZAway q) := by
  rw [pow_two, ← mul_assoc, qInv_mul_natCast_q, one_mul]

theorem slToAway_mennickeA_coe :
    ((slToAway q mennickeA : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![1, 0; 1, 1] := by
  rw [coe_slToAway, mennickeA_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

theorem slToAway_mennickeA_pow_coe (k : ℕ) :
    (((slToAway q mennickeA) ^ k : SL(2, ZAway q)) :
        Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![1, 0; ((k : ℕ) : ZAway q), 1] := by
  rw [← map_pow, coe_slToAway, mennickeA_pow_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

theorem mennickeU_mul_mennickeA_pow_sq :
    mennickeU q * (slToAway q mennickeA) ^ (q ^ 2) =
      slToAway q mennickeA * mennickeU q := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    slToAway_mennickeA_pow_coe, slToAway_mennickeA_coe, mennickeU_coe,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qInv_mul_natCast_q_sq q]

theorem mennickeU_inv_mul_mennickeA_mul_mennickeU :
    (mennickeU q)⁻¹ * slToAway q mennickeA * mennickeU q =
      (slToAway q mennickeA) ^ (q ^ 2) := by
  rw [mul_assoc, ← mennickeU_mul_mennickeA_pow_sq q, ← mul_assoc, inv_mul_cancel, one_mul]

def mennickeB : SL(2, ℤ) :=
  ⟨!![0, 1; -1, 0], by norm_num [Matrix.det_fin_two_of]⟩

@[scoped simp]
theorem mennickeB_coe :
    ((mennickeB : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![0, 1; -1, 0] := rfl

theorem mennickeB_inv_eq :
    (mennickeB)⁻¹ =
      (⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two_of]⟩ : SL(2, ℤ)) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  show (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℤ) * !![0, -1; 1, 0] = _
  rw [Matrix.mul_fin_two, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem slToAway_mennickeB_coe :
    ((slToAway q mennickeB : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![0, 1; -1, 0] := by
  rw [coe_slToAway, mennickeB_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

end GateSlice

section Lemma21AndEngines

variable (q m : ℕ) [NeZero q]

scoped instance mennickeZ_normal (hmq : Nat.Coprime m q) : (mennickeZ q m hmq).Normal := by
  haveI hmap : (Subgroup.map (QuotientGroup.mk' (mennickeQ q m))
      (principalCongruenceAway m q hmq)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rw [mennickeZ]
  exact Subgroup.Normal.comap inferInstance _

theorem mennickeA_pow_q_sq_sub_one_mem_of_mennickeU_mem
    (Z : Subgroup SL(2, ZAway q)) [hZN : Z.Normal] (hU : mennickeU q ∈ Z) :
    (slToAway q mennickeA) ^ (q ^ 2 - 1) ∈ Z := by
  have hq2 : q ^ 2 - 1 + 1 = q ^ 2 :=
    Nat.succ_pred_eq_of_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne q)) 2)
  have hkey : (slToAway q mennickeA) ^ (q ^ 2 - 1) =
      (mennickeU q)⁻¹ * (slToAway q mennickeA * mennickeU q *
        (slToAway q mennickeA)⁻¹) := by
    have h2 : (slToAway q mennickeA) ^ (q ^ 2 - 1) * slToAway q mennickeA =
        (slToAway q mennickeA) ^ (q ^ 2) := by
      rw [← pow_succ, hq2]
    have h3 : (slToAway q mennickeA) ^ (q ^ 2 - 1) =
        (slToAway q mennickeA) ^ (q ^ 2) * (slToAway q mennickeA)⁻¹ :=
      eq_mul_inv_of_mul_eq h2
    rw [h3, ← mennickeU_inv_mul_mennickeA_mul_mennickeU q]
    simp only [mul_assoc]
  rw [hkey]
  exact Z.mul_mem (Z.inv_mem hU)
    (hZN.conj_mem (mennickeU q) hU (slToAway q mennickeA))

theorem normalClosure_q_sq_sub_one_le_mennickeZ_of_lemma21 (hmq : Nat.Coprime m q)
    (h21 : MennickeLemma21 q m hmq) :
    Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ (q ^ 2 - 1)} : Set SL(2, ZAway q)) ≤
      mennickeZ q m hmq :=
  Subgroup.normalClosure_le_normal
    (Set.singleton_subset_iff.mpr
      (mennickeA_pow_q_sq_sub_one_mem_of_mennickeU_mem q (mennickeZ q m hmq) h21))

end Lemma21AndEngines

section Bridge

variable (N M q : ℕ)

theorem castHom_comp_zAwayToZMod (hMq : Nat.Coprime M q) (hNq : Nat.Coprime N q) (hNM : N ∣ M) :
    (ZMod.castHom hNM (ZMod N)).comp (zAwayToZMod M q hMq) = zAwayToZMod N q hNq := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (q : ℤ)) ?_
  ext a
  simp only [RingHom.comp_apply, zAwayToZMod_algebraMap, map_intCast]

end Bridge

end Ihara
p2m_reactivate "P2MW.S_Ihara_mennickeQ_le_commutator_sup_mennickeQ_mul.Ihara"

section Inl_CompositeEngines

namespace Ihara
p2m_export "Ihara" "mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff slToAway_mennickeA_pow_mem qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ mem_mennickeZ_iff MennickeLemma21 mennickeLemma21_iff ZAway slToAway coe_slToAway zAwayToZMod zAwayToZMod_algebraMap mennickeLemma21"
p2m_open "Ihara"

open Subgroup

open scoped commutatorElement

private theorem mem_of_coprime_pow_mem {G : Type*} [Group G] (Z : Subgroup G)
    {x : G} {a b : ℕ} (hab : Nat.Coprime a b) (ha : x ^ a ∈ Z) (hb : x ^ b ∈ Z) :
    x ∈ Z := by
  obtain ⟨u, v, huv⟩ := hab.isCoprime
  have h1 : (a : ℤ) * u + (b : ℤ) * v = 1 := by
    rw [mul_comm (a : ℤ) u, mul_comm (b : ℤ) v]; exact huv
  have hx : x = (x ^ a) ^ u * (x ^ b) ^ v := by
    rw [← zpow_natCast x a, ← zpow_natCast x b, ← zpow_mul, ← zpow_mul, ← zpow_add, h1,
      zpow_one]
  rw [hx]
  exact Z.mul_mem (Z.zpow_mem ha u) (Z.zpow_mem hb v)

section AbstractEngines

variable {G : Type*} [Group G]

theorem mem_of_torus_kill_data (D : Subgroup G) [hD : D.Normal]
    {g T : G} {a s : ℕ} (hs : 1 ≤ s)
    (hTg : ⁅T, g⁆ ∈ D)
    (hga : g ^ a ∈ D)
    (hconj : T⁻¹ * g * T * (g ^ s)⁻¹ ∈ D)
    (hcop : Nat.Coprime a (s - 1)) :
    g ∈ D := by

  have hmem : ∀ x : G, x ∈ D ↔ QuotientGroup.mk' D x = 1 := fun x => by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']

  have hcomm : QuotientGroup.mk' D T * QuotientGroup.mk' D g =
      QuotientGroup.mk' D g * QuotientGroup.mk' D T := by
    have h1 : QuotientGroup.mk' D ⁅T, g⁆ = 1 := (hmem _).mp hTg
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1

  have hconj1 : (QuotientGroup.mk' D T)⁻¹ * QuotientGroup.mk' D g * QuotientGroup.mk' D T =
      (QuotientGroup.mk' D g) ^ s := by
    have h1 : QuotientGroup.mk' D (T⁻¹ * g * T * (g ^ s)⁻¹) = 1 := (hmem _).mp hconj
    simp only [map_mul, map_inv, map_pow] at h1
    rwa [mul_inv_eq_one] at h1

  have hfix : (QuotientGroup.mk' D T)⁻¹ * QuotientGroup.mk' D g * QuotientGroup.mk' D T =
      QuotientGroup.mk' D g := by
    rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]

  have hgs : (QuotientGroup.mk' D g) ^ s = QuotientGroup.mk' D g := by
    rw [← hconj1, hfix]
  have hs1 : (QuotientGroup.mk' D g) ^ (s - 1) = 1 := by
    have h2 : (QuotientGroup.mk' D g) ^ (s - 1) * QuotientGroup.mk' D g =
        1 * QuotientGroup.mk' D g := by
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel hs, hgs]
    exact mul_right_cancel h2

  have ha1 : (QuotientGroup.mk' D g) ^ a = 1 := by
    rw [← map_pow]
    exact (hmem _).mp hga

  have hbot : QuotientGroup.mk' D g = 1 := by
    have h := mem_of_coprime_pow_mem
      (⊥ : Subgroup (G ⧸ D)) hcop (Subgroup.mem_bot.mpr ha1) (Subgroup.mem_bot.mpr hs1)
    exact Subgroup.mem_bot.mp h
  exact (hmem g).mpr hbot

theorem le_commutator_sup_of_forall_torus_kill (H Q₀ : Subgroup G)
    [hHn : H.Normal] [hQ₀n : Q₀.Normal] (S : Set G)
    (hS : S ⊆ ↑H)
    (hgen : H ≤ Subgroup.normalClosure S ⊔ Q₀)
    (hkill : ∀ g ∈ S, ∃ (T : G) (a s : ℕ), 1 ≤ s ∧ T ∈ H ∧
      g ^ a ∈ Q₀ ∧ T⁻¹ * g * T * (g ^ s)⁻¹ ∈ Q₀ ∧ Nat.Coprime a (s - 1)) :
    H ≤ ⁅H, H⁆ ⊔ Q₀ := by

  have hSD : S ⊆ ↑(⁅H, H⁆ ⊔ Q₀) := by
    intro g hg
    obtain ⟨T, a, s, hs, hTH, hga, hconj, hcop⟩ := hkill g hg
    rw [SetLike.mem_coe]
    exact mem_of_torus_kill_data _ hs
      (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hTH (hS hg)))
      (Subgroup.mem_sup_right hga) (Subgroup.mem_sup_right hconj) hcop

  have hNCD : Subgroup.normalClosure S ≤ ⁅H, H⁆ ⊔ Q₀ :=
    Subgroup.normalClosure_le_normal hSD

  exact le_trans hgen (sup_le hNCD le_sup_right)

theorem normalClosure_singleton_le_commutator_sup_of_torus_kill
    (g : G) (Q₀ : Subgroup G) [Q₀.Normal] {T : G} {a s : ℕ}
    (hs : 1 ≤ s)
    (hT : T ∈ Subgroup.normalClosure ({g} : Set G))
    (hga : g ^ a ∈ Q₀)
    (hconj : T⁻¹ * g * T * (g ^ s)⁻¹ ∈ Q₀)
    (hcop : Nat.Coprime a (s - 1)) :
    Subgroup.normalClosure ({g} : Set G) ≤
      ⁅Subgroup.normalClosure ({g} : Set G), Subgroup.normalClosure ({g} : Set G)⁆ ⊔ Q₀ := by
  refine le_commutator_sup_of_forall_torus_kill
    (Subgroup.normalClosure ({g} : Set G)) Q₀ ({g} : Set G) ?_ ?_ ?_
  · exact Subgroup.subset_normalClosure
  · exact le_sup_left
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨T, a, s, hs, hT, hga, hconj, hcop⟩

end AbstractEngines
p2m_reactivate "P2MW.S_Ihara_mennickeQ_le_commutator_sup_mennickeQ_mul.Ihara"

section ChainEngine

variable {G : Type*} [Group G]

private theorem chain_error_term_powers_eq_one {E : Type*} [Group E] (g T u : E)
    (s c a : ℕ) (hc : 1 ≤ c)
    (hkg : ∀ j : ℕ, Commute (T⁻¹ * g * T * (g ^ s)⁻¹) (g ^ j))
    (hku : Commute (T⁻¹ * g * T * (g ^ s)⁻¹) u)
    (hmg : ∀ j : ℕ, Commute (T⁻¹ * u⁻¹ * T * u) (g ^ j))
    (hmk : Commute (T⁻¹ * u⁻¹ * T * u) (T⁻¹ * g * T * (g ^ s)⁻¹))
    (hexact : ∀ j : ℕ, u⁻¹ * g ^ j * u = g ^ (j * c))
    (hga : g ^ a = 1) :
    (T⁻¹ * g * T * (g ^ s)⁻¹) ^ a = 1 ∧ (T⁻¹ * g * T * (g ^ s)⁻¹) ^ (c - 1) = 1 := by
  set k := T⁻¹ * g * T * (g ^ s)⁻¹ with hk_def
  set M := T⁻¹ * u⁻¹ * T * u with hM_def

  have hTgT : T⁻¹ * g * T = k * g ^ s := by
    rw [hk_def]; group

  have hconj_triv : ∀ x y : E, Commute x y → x⁻¹ * y * x = y := by
    intro x y h
    rw [h.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]

  have hconj_pow : ∀ n : ℕ, (T⁻¹ * g * T) ^ n = T⁻¹ * g ^ n * T := by
    intro n
    have h := conj_pow (i := n) (a := T⁻¹) (b := g)
    rwa [inv_inv] at h

  have part1 : k ^ a = 1 := by
    have hxy : Commute (T⁻¹ * g * T) ((g ^ s)⁻¹) := by
      rw [hTgT]
      exact Commute.mul_left ((hkg s).inv_right) ((Commute.refl (g ^ s)).inv_right)
    rw [hk_def, hxy.mul_pow, hconj_pow a, hga, mul_one, inv_mul_cancel, one_mul, inv_pow,
      ← pow_mul, Nat.mul_comm s a, pow_mul, hga, one_pow, inv_one]

  have hB1 : u⁻¹ * k * u = k ^ c := by

    have hsplit : u⁻¹ * k * u =
        M⁻¹ * (T⁻¹ * (u⁻¹ * g * u) * T) * M * (u⁻¹ * g ^ s * u)⁻¹ := by
      rw [hk_def, hM_def]; group

    have hexact1 : u⁻¹ * g * u = g ^ c := by
      have h := hexact 1
      rwa [pow_one, one_mul] at h
    rw [hexact1, hexact s] at hsplit

    have hconj_c : T⁻¹ * g ^ c * T = k ^ c * g ^ (s * c) := by
      rw [← hconj_pow c, hTgT, (hkg s).mul_pow, ← pow_mul]
    rw [hconj_c] at hsplit

    have hcommM : Commute M (k ^ c * g ^ (s * c)) :=
      Commute.mul_right (hmk.pow_right c) (hmg (s * c))
    have htriv : M⁻¹ * (k ^ c * g ^ (s * c)) * M = k ^ c * g ^ (s * c) :=
      hconj_triv M (k ^ c * g ^ (s * c)) hcommM
    rw [htriv] at hsplit
    rw [hsplit, mul_assoc, mul_inv_cancel, mul_one]

  have hB2 : u⁻¹ * k * u = k := hconj_triv u k hku.symm

  have part2 : k ^ (c - 1) = 1 := by
    have hkc : k ^ c = k := by rw [← hB1]; exact hB2
    have h2 : k ^ (c - 1) * k = 1 * k := by
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel hc, hkc]
    exact mul_right_cancel h2
  exact ⟨part1, part2⟩

theorem conj_pow_mem_of_centralizing_chain (Q N Z : Subgroup G)
    [hQn : Q.Normal] [hNn : N.Normal]
    (hZN : ∀ z ∈ Z, ∀ n ∈ N, ⁅z, n⁆ ∈ Q)
    {g T u : G} {s c a : ℕ}
    (hgZ : g ∈ Z) (hTZ : T ∈ Z) (huZ : u ∈ Z)
    (hkN : T⁻¹ * g * T * (g ^ s)⁻¹ ∈ N)
    (hnN : ⁅u, T⁆ ∈ N)
    (hexact : ∀ j : ℕ, u⁻¹ * g ^ j * u = g ^ (j * c))
    (hga : g ^ a ∈ Q)
    (hc : 1 ≤ c)
    (hcop : Nat.Coprime a (c - 1)) :
    T⁻¹ * g * T * (g ^ s)⁻¹ ∈ Q := by

  have hkZ : T⁻¹ * g * T * (g ^ s)⁻¹ ∈ Z :=
    Z.mul_mem (Z.mul_mem (Z.mul_mem (Z.inv_mem hTZ) hgZ) hTZ)
      (Z.inv_mem (Z.pow_mem hgZ s))

  have hMN : T⁻¹ * u⁻¹ * T * u ∈ N := by
    have h1 : (u * T)⁻¹ * ⁅u, T⁆⁻¹ * ((u * T)⁻¹)⁻¹ ∈ N :=
      hNn.conj_mem _ (N.inv_mem hnN) (u * T)⁻¹
    have heq : (u * T)⁻¹ * ⁅u, T⁆⁻¹ * ((u * T)⁻¹)⁻¹ = T⁻¹ * u⁻¹ * T * u := by
      simp only [commutatorElement_def, _root_.mul_inv_rev, inv_inv]
      group
    rwa [heq] at h1

  have hmem : ∀ x : G, x ∈ Q ↔ QuotientGroup.mk' Q x = 1 := fun x => by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']

  have hcommQ : ∀ z ∈ Z, ∀ n ∈ N,
      Commute (QuotientGroup.mk' Q z) (QuotientGroup.mk' Q n) := by
    intro z hz n hn
    have h1 : QuotientGroup.mk' Q ⁅z, n⁆ = 1 := (hmem _).mp (hZN z hz n hn)
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_commute.mp h1

  obtain ⟨h_a, h_c1⟩ := chain_error_term_powers_eq_one
    (QuotientGroup.mk' Q g) (QuotientGroup.mk' Q T) (QuotientGroup.mk' Q u) s c a hc

    (fun j => by
      have h := (hcommQ (g ^ j) (Z.pow_mem hgZ j) _ hkN).symm
      simp only [map_mul, map_inv, map_pow] at h
      exact h)

    (by
      have h := (hcommQ u huZ _ hkN).symm
      simp only [map_mul, map_inv, map_pow] at h
      exact h)

    (fun j => by
      have h := (hcommQ (g ^ j) (Z.pow_mem hgZ j) _ hMN).symm
      simp only [map_mul, map_inv, map_pow] at h
      exact h)

    (by
      have h := hcommQ _ hkZ _ hMN
      simp only [map_mul, map_inv, map_pow] at h
      exact h.symm)

    (fun j => by
      have h := congrArg (QuotientGroup.mk' Q) (hexact j)
      simpa only [map_mul, map_inv, map_pow] using h)

    (by
      have h := (hmem (g ^ a)).mp hga
      rwa [map_pow] at h)

  have hka : (T⁻¹ * g * T * (g ^ s)⁻¹) ^ a ∈ Q := by
    rw [hmem, map_pow]
    simp only [map_mul, map_inv, map_pow]
    exact h_a
  have hkc : (T⁻¹ * g * T * (g ^ s)⁻¹) ^ (c - 1) ∈ Q := by
    rw [hmem, map_pow]
    simp only [map_mul, map_inv, map_pow]
    exact h_c1

  exact mem_of_coprime_pow_mem Q hcop hka hkc

end ChainEngine
p2m_reactivate "P2MW.S_Ihara_mennickeQ_le_commutator_sup_mennickeQ_mul.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_mennickeQ_le_commutator_sup_mennickeQ_mul.Ihara"

end Inl_CompositeEngines
p2m_reactivate "P2MW.S_Ihara_mennickeQ_le_commutator_sup_mennickeQ_mul.Ihara"

section Inl_CompositeHabel

namespace Ihara
p2m_export "Ihara" "mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff slToAway_mennickeA_pow_mem qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ mem_mennickeZ_iff MennickeLemma21 mennickeLemma21_iff ZAway slToAway coe_slToAway zAwayToZMod zAwayToZMod_algebraMap mennickeLemma21"
p2m_open "Ihara"

open Subgroup Matrix

open scoped MatrixGroups

open scoped commutatorElement

section Shadow

variable (R : Type*) [CommRing R]

def shLower (v : R) : SL(2, R) :=
  ⟨!![1, 0; v, 1], by norm_num [Matrix.det_fin_two_of]⟩

theorem shLower_coe (v : R) :
    ((shLower R v : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![1, 0; v, 1] :=
  rfl

def shUpper (v : R) : SL(2, R) :=
  ⟨!![1, v; 0, 1], by norm_num [Matrix.det_fin_two_of]⟩

theorem shUpper_coe (v : R) :
    ((shUpper R v : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![1, v; 0, 1] :=
  rfl

def shRot : SL(2, R) :=
  ⟨!![0, 1; -1, 0], by norm_num [Matrix.det_fin_two_of]⟩

theorem shRot_coe : ((shRot R : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![0, 1; -1, 0] :=
  rfl

theorem shLower_mul (v w : R) : shLower R v * shLower R w = shLower R (v + w) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, shLower_coe, shLower_coe, shLower_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem shUpper_mul (v w : R) : shUpper R v * shUpper R w = shUpper R (v + w) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, shUpper_coe, shUpper_coe, shUpper_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp; try ring)

theorem shLower_zero : shLower R (0 : R) = 1 := by
  apply Subtype.ext
  rw [shLower_coe, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]

theorem shUpper_zero : shUpper R (0 : R) = 1 := by
  apply Subtype.ext
  rw [shUpper_coe, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]

theorem shLower_inv (v : R) : (shLower R v)⁻¹ = shLower R (-v) := by
  apply inv_eq_of_mul_eq_one_right
  rw [shLower_mul, show v + -v = (0 : R) by ring, shLower_zero]

theorem shUpper_inv (v : R) : (shUpper R v)⁻¹ = shUpper R (-v) := by
  apply inv_eq_of_mul_eq_one_right
  rw [shUpper_mul, show v + -v = (0 : R) by ring, shUpper_zero]

theorem shLower_one_pow (n : ℕ) : shLower R (1 : R) ^ n = shLower R (n : R) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, shLower_zero]
  | succ n ih => rw [pow_succ, ih, shLower_mul, Nat.cast_succ]

theorem shRot_mul_shLower (v : R) : shRot R * shLower R v = shUpper R (-v) * shRot R := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, shRot_coe, shLower_coe,
    shUpper_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem shRot_conj_shLower (v : R) : shRot R * shLower R v * (shRot R)⁻¹ = shUpper R (-v) := by
  rw [shRot_mul_shLower, mul_inv_cancel_right]

theorem shadow_torusWord_coe (x : R) (hx : 2 * x = 1) :
    ((shLower R x * shUpper R (-1) ^ 2 * shLower R x * (shUpper R (-1))⁻¹ * (shLower R 1)⁻¹ *
        (shUpper R (-1))⁻¹ : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) =
      !![2, 0; 0, x] := by
  have hc2 : shUpper R (-1) ^ 2 = shUpper R (-2) := by
    rw [pow_two, shUpper_mul]
    norm_num
  rw [hc2]
  simp only [shUpper_inv, shLower_inv, neg_neg]
  simp only [Matrix.SpecialLinearGroup.coe_mul, shLower_coe, shUpper_coe]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    (first
      | ring1
      | linear_combination (-1 : R) * hx
      | linear_combination hx
      | linear_combination (-x) * hx)

theorem shadow_torusWord_conj (x : R) (hx : 2 * x = 1) :
    (shLower R x * shUpper R (-1) ^ 2 * shLower R x * (shUpper R (-1))⁻¹ * (shLower R 1)⁻¹ *
        (shUpper R (-1))⁻¹)⁻¹ *
      shLower R 1 *
      (shLower R x * shUpper R (-1) ^ 2 * shLower R x * (shUpper R (-1))⁻¹ * (shLower R 1)⁻¹ *
        (shUpper R (-1))⁻¹) *
      (shLower R 1 ^ 4)⁻¹ = 1 := by
  have hT := shadow_torusWord_coe R x hx
  set W := shLower R x * shUpper R (-1) ^ 2 * shLower R x * (shUpper R (-1))⁻¹ *
      (shLower R 1)⁻¹ * (shUpper R (-1))⁻¹ with hW
  have h4 : shLower R 1 ^ 4 = shLower R 4 := by
    rw [shLower_one_pow]
    norm_num
  have hkey : shLower R 1 * W = W * shLower R 1 ^ 4 := by
    rw [h4]
    apply Subtype.ext
    have hL := Matrix.SpecialLinearGroup.coe_mul (shLower R 1) W
    have hR := Matrix.SpecialLinearGroup.coe_mul W (shLower R 4)
    rw [hL, hR, hT, shLower_coe, shLower_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> (simp; try (first | ring1 | linear_combination (-2 : R) * hx))
  calc W⁻¹ * shLower R 1 * W * (shLower R 1 ^ 4)⁻¹
      = W⁻¹ * (shLower R 1 * W) * (shLower R 1 ^ 4)⁻¹ := by group
    _ = W⁻¹ * (W * shLower R 1 ^ 4) * (shLower R 1 ^ 4)⁻¹ := by rw [hkey]
    _ = 1 := by group

theorem shadow_torusWord_conj_pow (x : R) (hx : 2 * x = 1) (n : ℕ) :
    (shLower R x * shUpper R (-1) ^ 2 * shLower R x * (shUpper R (-1))⁻¹ * (shLower R 1)⁻¹ *
        (shUpper R (-1))⁻¹)⁻¹ *
      shLower R 1 ^ n *
      (shLower R x * shUpper R (-1) ^ 2 * shLower R x * (shUpper R (-1))⁻¹ * (shLower R 1)⁻¹ *
        (shUpper R (-1))⁻¹) *
      ((shLower R 1 ^ n) ^ 4)⁻¹ = 1 := by
  set W := shLower R x * shUpper R (-1) ^ 2 * shLower R x * (shUpper R (-1))⁻¹ *
      (shLower R 1)⁻¹ * (shUpper R (-1))⁻¹ with hW
  have h1 : W⁻¹ * shLower R 1 * W = shLower R 1 ^ 4 := by
    have h := shadow_torusWord_conj R x hx
    rw [← hW] at h
    have h2 : W⁻¹ * shLower R 1 * W = W⁻¹ * shLower R 1 * W * (shLower R 1 ^ 4)⁻¹ * shLower R 1 ^ 4 := by
      group
    rw [h2, h, one_mul]
  have hconj : W⁻¹ * shLower R 1 ^ n * W = (W⁻¹ * shLower R 1 * W) ^ n := by
    have hcp := conj_pow (i := n) (a := W⁻¹) (b := shLower R 1)
    rw [inv_inv] at hcp
    exact hcp.symm
  calc W⁻¹ * shLower R 1 ^ n * W * ((shLower R 1 ^ n) ^ 4)⁻¹
      = (W⁻¹ * shLower R 1 * W) ^ n * ((shLower R 1 ^ n) ^ 4)⁻¹ := by rw [hconj]
    _ = (shLower R 1 ^ 4) ^ n * ((shLower R 1 ^ n) ^ 4)⁻¹ := by rw [h1]
    _ = (shLower R 1 ^ n) ^ 4 * ((shLower R 1 ^ n) ^ 4)⁻¹ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = 1 := mul_inv_cancel _

theorem shadow_torusWord_commute (x p w : R) (hx : 2 * x = 1) (u : SL(2, R))
    (hu : (u : Matrix (Fin 2) (Fin 2) R) = !![p, 0; 0, w]) :
    u * (shLower R x * shUpper R (-1) ^ 2 * shLower R x * (shUpper R (-1))⁻¹ * (shLower R 1)⁻¹ *
        (shUpper R (-1))⁻¹) =
      (shLower R x * shUpper R (-1) ^ 2 * shLower R x * (shUpper R (-1))⁻¹ * (shLower R 1)⁻¹ *
        (shUpper R (-1))⁻¹) * u := by
  have hT := shadow_torusWord_coe R x hx
  set W := shLower R x * shUpper R (-1) ^ 2 * shLower R x * (shUpper R (-1))⁻¹ *
      (shLower R 1)⁻¹ * (shUpper R (-1))⁻¹ with hW
  apply Subtype.ext
  have hL := Matrix.SpecialLinearGroup.coe_mul u W
  have hR := Matrix.SpecialLinearGroup.coe_mul W u
  rw [hL, hR, hT, hu, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

end Shadow
p2m_reactivate "P2MW.S_Ihara_mennickeQ_le_commutator_sup_mennickeQ_mul.Ihara"

section Arithmetic

theorem two_dvd_sq_sub_one_of_not_dvd {q : ℕ} (hq : ¬ 2 ∣ q) : 2 ∣ q ^ 2 - 1 := by
  obtain ⟨k, hk⟩ : ∃ k, q = 2 * k + 1 := ⟨q / 2, by omega⟩
  refine ⟨2 * (k * k) + 2 * k, ?_⟩
  have hq2 : q ^ 2 = 2 * (2 * (k * k) + 2 * k) + 1 := by rw [hk]; ring
  rw [hq2, Nat.add_sub_cancel]

theorem three_dvd_sq_sub_one_of_not_dvd {q : ℕ} (hq : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  obtain ⟨k, hk⟩ : ∃ k, q = 3 * k + 1 ∨ q = 3 * k + 2 := ⟨q / 3, by omega⟩
  rcases hk with h | h
  · refine ⟨3 * (k * k) + 2 * k, ?_⟩
    have hq2 : q ^ 2 = 3 * (3 * (k * k) + 2 * k) + 1 := by rw [h]; ring
    rw [hq2, Nat.add_sub_cancel]
  · refine ⟨3 * (k * k) + 4 * k + 1, ?_⟩
    have hq2 : q ^ 2 = 3 * (3 * (k * k) + 4 * k + 1) + 1 := by rw [h]; ring
    rw [hq2, Nat.add_sub_cancel]

theorem three_lt_of_prime_dvd_of_coprime (q m' : ℕ) {p : ℕ} (hp : p.Prime) (hpm : p ∣ m')
    (hm'q : Nat.Coprime m' q) (hm'n : Nat.Coprime m' (q ^ 2 - 1)) : 3 < p := by
  have hnotq : ¬ p ∣ q := by
    intro h
    have hgcd : Nat.gcd m' q = 1 := hm'q
    have hp1 : p ∣ 1 := hgcd ▸ Nat.dvd_gcd hpm h
    exact hp.one_lt.ne' (Nat.dvd_one.mp hp1)
  have hnotn : ¬ p ∣ q ^ 2 - 1 := by
    intro h
    have hgcd : Nat.gcd m' (q ^ 2 - 1) = 1 := hm'n
    have hp1 : p ∣ 1 := hgcd ▸ Nat.dvd_gcd hpm h
    exact hp.one_lt.ne' (Nat.dvd_one.mp hp1)
  by_contra hle
  rw [not_lt] at hle
  have h23 : p = 2 ∨ p = 3 := by
    have h2 := hp.two_le
    omega
  rcases h23 with rfl | rfl
  · exact hnotn (two_dvd_sq_sub_one_of_not_dvd hnotq)
  · exact hnotn (three_dvd_sq_sub_one_of_not_dvd hnotq)

theorem coprime_three_of_coprime (q m' : ℕ) (hm'q : Nat.Coprime m' q)
    (hm'n : Nat.Coprime m' (q ^ 2 - 1)) : Nat.Coprime m' 3 := by
  have h3 : Nat.Coprime 3 m' := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_
    intro h3d
    have h := three_lt_of_prime_dvd_of_coprime q m' Nat.prime_three h3d hm'q hm'n
    omega
  exact h3.symm

theorem not_two_dvd_of_coprime (q m' : ℕ) (hm'q : Nat.Coprime m' q)
    (hm'n : Nat.Coprime m' (q ^ 2 - 1)) : ¬ 2 ∣ m' := by
  intro h2
  have h := three_lt_of_prime_dvd_of_coprime q m' Nat.prime_two h2 hm'q hm'n
  omega

def torusBeta (m' : ℕ) : ℕ := (m' + 1) / 2

theorem two_mul_torusBeta (m' : ℕ) (h : ¬ 2 ∣ m') : 2 * torusBeta m' = m' + 1 := by
  simp only [torusBeta]
  omega

theorem torusBeta_cast (q m' : ℕ) (hm'q : Nat.Coprime m' q) (hm'n : Nat.Coprime m' (q ^ 2 - 1)) :
    2 * ((torusBeta m' : ℕ) : ZMod m') = 1 := by
  have hodd := not_two_dvd_of_coprime q m' hm'q hm'n
  have h := two_mul_torusBeta m' hodd
  have h2 : ((2 * torusBeta m' : ℕ) : ZMod m') = ((m' + 1 : ℕ) : ZMod m') := by
    rw [h]
  push_cast at h2
  rwa [ZMod.natCast_self, zero_add] at h2

def crtSplitExp (m' m'' : ℕ) (hcop : Nat.Coprime m' m'') : ℕ :=
  (Nat.chineseRemainder hcop 1 0 : ℕ)

theorem crtSplitExp_modEq_one (m' m'' : ℕ) (hcop : Nat.Coprime m' m'') :
    crtSplitExp m' m'' hcop ≡ 1 [MOD m'] :=
  (Nat.chineseRemainder hcop 1 0).2.1

theorem crtSplitExp_modEq_zero (m' m'' : ℕ) (hcop : Nat.Coprime m' m'') :
    crtSplitExp m' m'' hcop ≡ 0 [MOD m''] :=
  (Nat.chineseRemainder hcop 1 0).2.2

theorem dvd_crtSplitExp (m' m'' : ℕ) (hcop : Nat.Coprime m' m'') : m'' ∣ crtSplitExp m' m'' hcop :=
  (Nat.modEq_zero_iff_dvd).mp (crtSplitExp_modEq_zero m' m'' hcop)

end Arithmetic
p2m_reactivate "P2MW.S_Ihara_mennickeQ_le_commutator_sup_mennickeQ_mul.Ihara"

section Reductions

variable (q : ℕ)

theorem slAwayReduction_eq_map_castHom (m m' : ℕ) (hdvd : m' ∣ m) (hmq : Nat.Coprime m q)
    (hm'q : Nat.Coprime m' q) (x : SL(2, ZAway q)) :
    slAwayReduction m' q hm'q x =
      Matrix.SpecialLinearGroup.map (ZMod.castHom hdvd (ZMod m')) (slAwayReduction m q hmq x) := by
  refine Subtype.ext ?_
  have hR : ((Matrix.SpecialLinearGroup.map (ZMod.castHom hdvd (ZMod m'))
      (slAwayReduction m q hmq x) : SL(2, ZMod m')) : Matrix (Fin 2) (Fin 2) (ZMod m')) =
      (((x : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)).map
        (zAwayToZMod m q hmq)).map (ZMod.castHom hdvd (ZMod m')) := by
    rw [← slAwayReduction_coe]
    rfl
  rw [slAwayReduction_coe, hR, Matrix.map_map]
  ext i j
  simp only [Matrix.map_apply, Function.comp_apply]
  exact (DFunLike.congr_fun (castHom_comp_zAwayToZMod m' m q hmq hm'q hdvd)
    (((x : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) i j)).symm

theorem zmod_eq_of_castHom_eq {m' m'' : ℕ} [NeZero m'] [NeZero m''] (hcop : Nat.Coprime m' m'')
    {x y : ZMod (m' * m'')}
    (h1 : ZMod.castHom (dvd_mul_right m' m'') (ZMod m') x = ZMod.castHom (dvd_mul_right m' m'') (ZMod m') y)
    (h2 : ZMod.castHom (dvd_mul_left m'' m') (ZMod m'') x = ZMod.castHom (dvd_mul_left m'' m') (ZMod m'') y) :
    x = y := by
  haveI : NeZero (m' * m'') := ⟨Nat.mul_ne_zero (NeZero.ne m') (NeZero.ne m'')⟩
  rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y] at h1 h2 ⊢
  rw [map_natCast, map_natCast, ZMod.natCast_eq_natCast_iff] at h1 h2
  rw [ZMod.natCast_eq_natCast_iff]
  exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, h2⟩

theorem principalCongruenceAway_mul_eq_inf (m' m'' : ℕ) [NeZero m'] [NeZero m'']
    (hcop : Nat.Coprime m' m'') (hm'q : Nat.Coprime m' q) (hm''q : Nat.Coprime m'' q)
    (hmq : Nat.Coprime (m' * m'') q) :
    principalCongruenceAway (m' * m'') q hmq =
      principalCongruenceAway m' q hm'q ⊓ principalCongruenceAway m'' q hm''q := by
  refine le_antisymm (le_inf ?_ ?_) ?_
  · intro x hx
    rw [mem_principalCongruenceAway_iff] at hx ⊢
    rw [slAwayReduction_eq_map_castHom q (m' * m'') m' (dvd_mul_right m' m'') hmq hm'q, hx, map_one]
  · intro x hx
    rw [mem_principalCongruenceAway_iff] at hx ⊢
    rw [slAwayReduction_eq_map_castHom q (m' * m'') m'' (dvd_mul_left m'' m') hmq hm''q, hx, map_one]
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [mem_principalCongruenceAway_iff] at hx1 hx2 ⊢
    have key1 : Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_right m' m'') (ZMod m'))
        (slAwayReduction (m' * m'') q hmq x) =
        Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_right m' m'') (ZMod m'))
          (1 : SL(2, ZMod (m' * m''))) := by
      rw [map_one, ← slAwayReduction_eq_map_castHom q (m' * m'') m' (dvd_mul_right m' m'') hmq hm'q]
      exact hx1
    have key2 : Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_left m'' m') (ZMod m''))
        (slAwayReduction (m' * m'') q hmq x) =
        Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_left m'' m') (ZMod m''))
          (1 : SL(2, ZMod (m' * m''))) := by
      rw [map_one, ← slAwayReduction_eq_map_castHom q (m' * m'') m'' (dvd_mul_left m'' m') hmq hm''q]
      exact hx2
    refine Subtype.ext ?_
    ext i j
    refine zmod_eq_of_castHom_eq hcop ?_ ?_
    · exact congrFun (congrFun (congrArg Subtype.val key1) i) j
    · exact congrFun (congrFun (congrArg Subtype.val key2) i) j

theorem slToAway_mennickeA_pow_mem_principalCongruenceAway_iff (r : ℕ) (hrq : Nat.Coprime r q) (k : ℕ) :
    (slToAway q mennickeA) ^ k ∈ principalCongruenceAway r q hrq ↔ r ∣ k := by
  constructor
  · intro hmem
    rw [mem_principalCongruenceAway_iff] at hmem
    have hmat := congrArg (fun g : SL(2, ZMod r) => (g : Matrix (Fin 2) (Fin 2) (ZMod r))) hmem
    rw [slAwayReduction_coe, slToAway_mennickeA_pow_coe, Matrix.SpecialLinearGroup.coe_one] at hmat
    have h10 := congrFun (congrFun hmat 1) 0
    rw [Matrix.map_apply, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at h10
    have hval : (!![1, 0; ((k : ℕ) : ZAway q), 1] : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0 =
        ((k : ℕ) : ZAway q) := by simp
    rw [hval, map_natCast] at h10
    exact (ZMod.natCast_eq_zero_iff k r).mp h10
  · rintro ⟨c, rfl⟩
    rw [pow_mul]
    exact pow_mem (slToAway_mennickeA_pow_mem r q hrq) c

theorem slAwayReduction_slToAway_mennickeA_eq_shLower (r : ℕ) (hrq : Nat.Coprime r q) :
    slAwayReduction r q hrq (slToAway q mennickeA) = shLower (ZMod r) 1 := by
  apply Subtype.ext
  rw [slAwayReduction_coe, slToAway_mennickeA_coe, shLower_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

theorem slAwayReduction_slToAway_mennickeB (r : ℕ) (hrq : Nat.Coprime r q) :
    slAwayReduction r q hrq (slToAway q mennickeB) = shRot (ZMod r) := by
  apply Subtype.ext
  rw [slAwayReduction_coe, slToAway_mennickeB_coe, shRot_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply, map_neg]

theorem slAwayReduction_mennickeU_coe (r : ℕ) (hrq : Nat.Coprime r q) :
    ((slAwayReduction r q hrq (mennickeU q) : SL(2, ZMod r)) : Matrix (Fin 2) (Fin 2) (ZMod r)) =
      !![((q : ℕ) : ZMod r), 0; 0, zAwayToZMod r q hrq (qInv q)] := by
  rw [slAwayReduction_coe, mennickeU_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply, map_natCast]

end Reductions
p2m_reactivate "P2MW.S_Ihara_mennickeQ_le_commutator_sup_mennickeQ_mul.Ihara"

section TorusWord

variable (q : ℕ)

noncomputable def blockA (m' m'' : ℕ) (hcop : Nat.Coprime m' m'') : SL(2, ZAway q) :=
  (slToAway q mennickeA) ^ (crtSplitExp m' m'' hcop)

noncomputable def blockC (m' m'' : ℕ) (hcop : Nat.Coprime m' m'') : SL(2, ZAway q) :=
  (slToAway q mennickeB) * blockA q m' m'' hcop * (slToAway q mennickeB)⁻¹

noncomputable def torusWord (m' m'' : ℕ) (hcop : Nat.Coprime m' m'') : SL(2, ZAway q) :=
  blockA q m' m'' hcop ^ torusBeta m' * blockC q m' m'' hcop ^ 2 * blockA q m' m'' hcop ^ torusBeta m' *
    (blockC q m' m'' hcop)⁻¹ * (blockA q m' m'' hcop)⁻¹ * (blockC q m' m'' hcop)⁻¹

theorem torusWord_def (m' m'' : ℕ) (hcop : Nat.Coprime m' m'') :
    torusWord q m' m'' hcop =
      blockA q m' m'' hcop ^ torusBeta m' * blockC q m' m'' hcop ^ 2 *
        blockA q m' m'' hcop ^ torusBeta m' * (blockC q m' m'' hcop)⁻¹ * (blockA q m' m'' hcop)⁻¹ *
        (blockC q m' m'' hcop)⁻¹ :=
  rfl

theorem blockA_mem_mennickeQ (m' m'' : ℕ) (hcop : Nat.Coprime m' m'') :
    blockA q m' m'' hcop ∈ mennickeQ q m'' := by
  obtain ⟨c, hc⟩ := dvd_crtSplitExp m' m'' hcop
  have hmem : (slToAway q mennickeA) ^ m'' ∈ mennickeQ q m'' :=
    Subgroup.subset_normalClosure (Set.mem_singleton _)
  have heq : blockA q m' m'' hcop = ((slToAway q mennickeA) ^ m'') ^ c := by
    rw [blockA, hc, ← pow_mul]
  rw [heq]
  exact pow_mem hmem c

theorem blockC_mem_mennickeQ (m' m'' : ℕ) (hcop : Nat.Coprime m' m'') :
    blockC q m' m'' hcop ∈ mennickeQ q m'' := by
  show (slToAway q mennickeB) * blockA q m' m'' hcop * (slToAway q mennickeB)⁻¹ ∈ _
  exact Subgroup.normalClosure_normal.conj_mem _ (blockA_mem_mennickeQ q m' m'' hcop) (slToAway q mennickeB)

theorem torusWord_mem_mennickeQ (m' m'' : ℕ) (hcop : Nat.Coprime m' m'') :
    torusWord q m' m'' hcop ∈ mennickeQ q m'' := by
  have hA := blockA_mem_mennickeQ q m' m'' hcop
  have hB := blockC_mem_mennickeQ q m' m'' hcop
  rw [torusWord_def]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (pow_mem hA _) (pow_mem hB 2)) (pow_mem hA _))
    (inv_mem hB)) (inv_mem hA)) (inv_mem hB)

theorem slAwayReduction_blockA (m' m'' : ℕ) (hcop : Nat.Coprime m' m'') (hm'q : Nat.Coprime m' q) :
    slAwayReduction m' q hm'q (blockA q m' m'' hcop) = shLower (ZMod m') 1 := by
  rw [blockA, map_pow, slAwayReduction_slToAway_mennickeA_eq_shLower q m' hm'q, shLower_one_pow]
  have hcast : ((crtSplitExp m' m'' hcop : ℕ) : ZMod m') = 1 := by
    have hmod := crtSplitExp_modEq_one m' m'' hcop
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    simpa using h
  rw [hcast]

theorem slAwayReduction_blockA_self (m' m'' : ℕ) (hcop : Nat.Coprime m' m'') (hm''q : Nat.Coprime m'' q) :
    slAwayReduction m'' q hm''q (blockA q m' m'' hcop) = 1 := by
  have hmem : blockA q m' m'' hcop ∈ principalCongruenceAway m'' q hm''q := by
    rw [blockA]
    exact (slToAway_mennickeA_pow_mem_principalCongruenceAway_iff q m'' hm''q _).mpr
      (dvd_crtSplitExp m' m'' hcop)
  rwa [mem_principalCongruenceAway_iff] at hmem

theorem slAwayReduction_blockC (m' m'' : ℕ) (hcop : Nat.Coprime m' m'') (hm'q : Nat.Coprime m' q) :
    slAwayReduction m' q hm'q (blockC q m' m'' hcop) = shUpper (ZMod m') (-1) := by
  rw [blockC, map_mul, map_mul, map_inv, slAwayReduction_slToAway_mennickeB q m' hm'q,
    slAwayReduction_blockA q m' m'' hcop hm'q]
  exact shRot_conj_shLower (ZMod m') 1

theorem slAwayReduction_blockC_self (m' m'' : ℕ) (hcop : Nat.Coprime m' m'') (hm''q : Nat.Coprime m'' q) :
    slAwayReduction m'' q hm''q (blockC q m' m'' hcop) = 1 := by
  rw [blockC, map_mul, map_mul, map_inv, slAwayReduction_blockA_self q m' m'' hcop hm''q]
  group

theorem slAwayReduction_torusWord (m' m'' : ℕ) (hcop : Nat.Coprime m' m'') (hm'q : Nat.Coprime m' q) :
    slAwayReduction m' q hm'q (torusWord q m' m'' hcop) =
      shLower (ZMod m') ((torusBeta m' : ℕ) : ZMod m') * shUpper (ZMod m') (-1) ^ 2 *
        shLower (ZMod m') ((torusBeta m' : ℕ) : ZMod m') * (shUpper (ZMod m') (-1))⁻¹ *
        (shLower (ZMod m') 1)⁻¹ * (shUpper (ZMod m') (-1))⁻¹ := by
  rw [torusWord_def]
  simp only [map_mul, map_pow, map_inv]
  rw [slAwayReduction_blockA q m' m'' hcop hm'q, slAwayReduction_blockC q m' m'' hcop hm'q, shLower_one_pow]

theorem slAwayReduction_torusWord_self (m' m'' : ℕ) (hcop : Nat.Coprime m' m'') (hm''q : Nat.Coprime m'' q) :
    slAwayReduction m'' q hm''q (torusWord q m' m'' hcop) = 1 := by
  rw [torusWord_def]
  simp only [map_mul, map_pow, map_inv]
  rw [slAwayReduction_blockA_self q m' m'' hcop hm''q, slAwayReduction_blockC_self q m' m'' hcop hm''q]
  simp

theorem torusWord_conj_mem_principalCongruenceAway (m' m'' : ℕ) [NeZero m'] [NeZero m'']
    (hcop : Nat.Coprime m' m'') (hm'q : Nat.Coprime m' q) (hm''q : Nat.Coprime m'' q)
    (hmq : Nat.Coprime (m' * m'') q) (hm'n : Nat.Coprime m' (q ^ 2 - 1)) :
    (torusWord q m' m'' hcop)⁻¹ * (slToAway q mennickeA) ^ m'' * torusWord q m' m'' hcop *
        (((slToAway q mennickeA) ^ m'') ^ 4)⁻¹ ∈
      principalCongruenceAway (m' * m'') q hmq := by
  rw [principalCongruenceAway_mul_eq_inf q m' m'' hcop hm'q hm''q hmq, Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [mem_principalCongruenceAway_iff]
    simp only [map_mul, map_inv, map_pow]
    rw [slAwayReduction_torusWord q m' m'' hcop hm'q, slAwayReduction_slToAway_mennickeA_eq_shLower q m' hm'q]
    exact shadow_torusWord_conj_pow (ZMod m') ((torusBeta m' : ℕ) : ZMod m') (torusBeta_cast q m' hm'q hm'n)
      m''
  · rw [mem_principalCongruenceAway_iff]
    simp only [map_mul, map_inv, map_pow]
    rw [slAwayReduction_torusWord_self q m' m'' hcop hm''q]
    have hA1 : slAwayReduction m'' q hm''q ((slToAway q mennickeA) ^ m'') = 1 := by
      rw [← mem_principalCongruenceAway_iff]
      exact slToAway_mennickeA_pow_mem m'' q hm''q
    rw [map_pow] at hA1
    rw [hA1]
    simp

theorem commutator_mennickeU_torusWord_mem_principalCongruenceAway (m' m'' : ℕ) [NeZero m'] [NeZero m'']
    (hcop : Nat.Coprime m' m'') (hm'q : Nat.Coprime m' q) (hm''q : Nat.Coprime m'' q)
    (hmq : Nat.Coprime (m' * m'') q) (hm'n : Nat.Coprime m' (q ^ 2 - 1)) :
    ⁅mennickeU q, torusWord q m' m'' hcop⁆ ∈ principalCongruenceAway (m' * m'') q hmq := by
  rw [principalCongruenceAway_mul_eq_inf q m' m'' hcop hm'q hm''q hmq, Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [mem_principalCongruenceAway_iff, map_commutatorElement, commutatorElement_eq_one_iff_commute,
      slAwayReduction_torusWord q m' m'' hcop hm'q]
    exact shadow_torusWord_commute (ZMod m') ((torusBeta m' : ℕ) : ZMod m') ((q : ℕ) : ZMod m')
      (zAwayToZMod m' q hm'q (qInv q)) (torusBeta_cast q m' hm'q hm'n) (slAwayReduction m' q hm'q (mennickeU q))
      (slAwayReduction_mennickeU_coe q m' hm'q)
  · rw [mem_principalCongruenceAway_iff, map_commutatorElement, slAwayReduction_torusWord_self q m' m'' hcop hm''q,
      commutatorElement_one_right]

end TorusWord
p2m_reactivate "P2MW.S_Ihara_mennickeQ_le_commutator_sup_mennickeQ_mul.Ihara"

section Habel

variable (q : ℕ)

theorem mennickeU_inv_conj_mennickeA_pow_pow (d j : ℕ) :
    (mennickeU q)⁻¹ * ((slToAway q mennickeA) ^ d) ^ j * mennickeU q =
      ((slToAway q mennickeA) ^ d) ^ (j * q ^ 2) := by
  rw [← pow_mul, ← pow_mul]
  have h1 : ((mennickeU q)⁻¹ * slToAway q mennickeA * mennickeU q) ^ (d * j) =
      (mennickeU q)⁻¹ * (slToAway q mennickeA) ^ (d * j) * mennickeU q := by
    have h := conj_pow (i := d * j) (a := (mennickeU q)⁻¹) (b := slToAway q mennickeA)
    rwa [inv_inv] at h
  rw [← h1, mennickeU_inv_mul_mennickeA_mul_mennickeU q, ← pow_mul]
  congr 1
  ring

theorem mennickeQ_le_of_dvd (a b : ℕ) (hdvd : a ∣ b) : mennickeQ q b ≤ mennickeQ q a := by
  apply Subgroup.normalClosure_le_normal
  rw [Set.singleton_subset_iff]
  obtain ⟨c, rfl⟩ := hdvd
  rw [pow_mul]
  exact pow_mem (Subgroup.subset_normalClosure (Set.mem_singleton _)) c

variable [NeZero q]

theorem mennickeQ_le_mennickeZ_of_dvd (m m'' : ℕ) (hmq : Nat.Coprime m q) (hdvd : (q ^ 2 - 1) ∣ m'') :
    mennickeQ q m'' ≤ mennickeZ q m hmq :=
  le_trans (mennickeQ_le_of_dvd q (q ^ 2 - 1) m'' hdvd)
    (normalClosure_q_sq_sub_one_le_mennickeZ_of_lemma21 q m hmq (mennickeLemma21 q m hmq))

theorem mennickeQ_le_commutator_sup_of_torusData (m' m'' : ℕ) (hmq : Nat.Coprime (m' * m'') q)
    (hcentral : mennickeQ q m'' ≤ mennickeZ q (m' * m'') hmq)
    (T : SL(2, ZAway q)) (s : ℕ) (hs : 1 ≤ s) (hT : T ∈ mennickeQ q m'')
    (hkN : T⁻¹ * (slToAway q mennickeA) ^ m'' * T * (((slToAway q mennickeA) ^ m'') ^ s)⁻¹ ∈
      principalCongruenceAway (m' * m'') q hmq)
    (hnN : ⁅mennickeU q, T⁆ ∈ principalCongruenceAway (m' * m'') q hmq)
    (hcop_s : Nat.Coprime m' (s - 1)) (hcop_q : Nat.Coprime m' (q ^ 2 - 1)) :
    mennickeQ q m'' ≤ ⁅mennickeQ q m'', mennickeQ q m''⁆ ⊔ mennickeQ q (m' * m'') := by

  have hgZ : (slToAway q mennickeA) ^ m'' ∈ mennickeZ q (m' * m'') hmq :=
    hcentral (Subgroup.subset_normalClosure (Set.mem_singleton _))
  have hTZ : T ∈ mennickeZ q (m' * m'') hmq := hcentral hT
  have huZ : mennickeU q ∈ mennickeZ q (m' * m'') hmq :=
    (mennickeLemma21_iff q (m' * m'') hmq).mp (mennickeLemma21 q (m' * m'') hmq)

  have hZN : ∀ z ∈ mennickeZ q (m' * m'') hmq, ∀ n ∈ principalCongruenceAway (m' * m'') q hmq,
      ⁅z, n⁆ ∈ mennickeQ q (m' * m'') := by
    intro z hz n hn
    exact (mem_mennickeZ_iff q (m' * m'') hmq z).mp hz n hn

  have hga : ((slToAway q mennickeA) ^ m'') ^ m' ∈ mennickeQ q (m' * m'') := by
    have heq : ((slToAway q mennickeA) ^ m'') ^ m' = (slToAway q mennickeA) ^ (m' * m'') := by
      rw [← pow_mul, Nat.mul_comm]
    rw [heq]
    exact Subgroup.subset_normalClosure (Set.mem_singleton _)
  have hc : 1 ≤ q ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (NeZero.ne q))

  have hconj_Q : T⁻¹ * (slToAway q mennickeA) ^ m'' * T * (((slToAway q mennickeA) ^ m'') ^ s)⁻¹ ∈
      mennickeQ q (m' * m'') :=
    conj_pow_mem_of_centralizing_chain (mennickeQ q (m' * m'')) (principalCongruenceAway (m' * m'') q hmq)
      (mennickeZ q (m' * m'') hmq) hZN hgZ hTZ huZ hkN hnN (mennickeU_inv_conj_mennickeA_pow_pow q m'') hga hc
      hcop_q

  exact normalClosure_singleton_le_commutator_sup_of_torus_kill ((slToAway q mennickeA) ^ m'')
    (mennickeQ q (m' * m'')) hs hT hga hconj_Q hcop_s

theorem mennickeQ_le_commutator_sup_mennickeQ_mul_impl (m' m'' : ℕ) [NeZero m'] [NeZero m'']
    (hcop : Nat.Coprime m' m'') (hm'q : Nat.Coprime m' q) (hm''q : Nat.Coprime m'' q)
    (hmq : Nat.Coprime (m' * m'') q) (hm'n : Nat.Coprime m' (q ^ 2 - 1)) (hsat : (q ^ 2 - 1) ∣ m'') :
    mennickeQ q m'' ≤ ⁅mennickeQ q m'', mennickeQ q m''⁆ ⊔ mennickeQ q (m' * m'') := by
  refine mennickeQ_le_commutator_sup_of_torusData q m' m'' hmq
    (mennickeQ_le_mennickeZ_of_dvd q (m' * m'') m'' hmq hsat) (torusWord q m' m'' hcop) 4 (by norm_num)
    (torusWord_mem_mennickeQ q m' m'' hcop)
    (torusWord_conj_mem_principalCongruenceAway q m' m'' hcop hm'q hm''q hmq hm'n)
    (commutator_mennickeU_torusWord_mem_principalCongruenceAway q m' m'' hcop hm'q hm''q hmq hm'n) ?_ hm'n
  have h41 : (4 : ℕ) - 1 = 3 := by norm_num
  rw [h41]
  exact coprime_three_of_coprime q m' hm'q hm'n

end Habel
p2m_reactivate "P2MW.S_Ihara_mennickeQ_le_commutator_sup_mennickeQ_mul.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_mennickeQ_le_commutator_sup_mennickeQ_mul.Ihara"

end Inl_CompositeHabel
p2m_reactivate "P2MW.S_Ihara_mennickeQ_le_commutator_sup_mennickeQ_mul.Ihara"

open scoped MatrixGroups in
theorem solution (q : ℕ) [NeZero q] (m' m'' : ℕ) [NeZero m']
    [NeZero m''] (hcop : Nat.Coprime m' m'') (hm'q : Nat.Coprime m' q) (hm''q : Nat.Coprime m'' q)
    (hmq : Nat.Coprime (m' * m'') q) (hm'n : Nat.Coprime m' (q ^ 2 - 1)) (hsat : q ^ 2 - 1 ∣ m'') :
    Ihara.mennickeQ q m'' ≤ ⁅Ihara.mennickeQ q m'', Ihara.mennickeQ q m''⁆ ⊔ Ihara.mennickeQ q (m' * m'') :=
  Ihara.mennickeQ_le_commutator_sup_mennickeQ_mul_impl q m' m'' hcop hm'q hm''q hmq hm'n hsat

#print axioms solution

end S_Ihara_mennickeQ_le_commutator_sup_mennickeQ_mul
end P2MW
export P2MW.S_Ihara_mennickeQ_le_commutator_sup_mennickeQ_mul (solution)
