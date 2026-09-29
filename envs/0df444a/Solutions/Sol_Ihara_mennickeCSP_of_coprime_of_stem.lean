-- Prove2me | solution 1 for Ihara.mennickeCSP_of_coprime_of_stem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7dce39d2-3f79-50a3-920a-e518f998cbc9

import Definitions.Def_IharaMennickeCarrier
import Definitions.Def_SchurMultiplierTrivial
import Theorems.Thm_Ihara_mennickeLemma21
import Theorems.Thm_Ihara_normalClosure_mennickeA_eq_top
import Mathlib.GroupTheory.QuotientGroup.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_mennickeCSP_of_coprime_of_stem

set_option autoImplicit false

namespace SolH7a

open Matrix
open scoped MatrixGroups commutatorElement
open Subgroup
open Ihara

universe u

private theorem sl2coe_mul_h7a {R : Type*} [CommRing R] (A B : SL(2, R)) :
    ((A * B : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) * B := rfl

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
  rw [sl2coe_mul_h7a, sl2coe_mul_h7a,
    slToAway_mennickeA_pow_coe, slToAway_mennickeA_coe, mennickeU_coe,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qInv_mul_natCast_q_sq q]

theorem mennickeU_inv_mul_mennickeA_mul_mennickeU :
    (mennickeU q)⁻¹ * slToAway q mennickeA * mennickeU q =
      (slToAway q mennickeA) ^ (q ^ 2) := by
  rw [mul_assoc, ← mennickeU_mul_mennickeA_pow_sq q, ← mul_assoc, inv_mul_cancel, one_mul]

end GateSlice

section Centrality
variable (q : ℕ) [NeZero q]

scoped instance mennickeZ_normal {m : ℕ} (hmq : Nat.Coprime m q) : (mennickeZ q m hmq).Normal := by
  haveI hmap : (Subgroup.map (QuotientGroup.mk' (mennickeQ q m))
      (principalCongruenceAway m q hmq)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rw [mennickeZ]
  exact Subgroup.Normal.comap inferInstance _

theorem eq_top_of_normal_of_mennickeA_mem (Z : Subgroup SL(2, ZAway q)) [Z.Normal]
    (hA : slToAway q mennickeA ∈ Z) : Z = ⊤ := by
  rw [← top_le_iff, ← Ihara.normalClosure_mennickeA_eq_top q]
  exact Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hA)

omit [NeZero q] in

theorem mennickeA_pow_mem_mennickeZ {m : ℕ} (hmq : Nat.Coprime m q) :
    (slToAway q mennickeA) ^ m ∈ mennickeZ q m hmq :=
  mennickeQ_le_mennickeZ q m hmq
    (Subgroup.subset_normalClosure (Set.mem_singleton _))

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

theorem mem_of_pow_mem_of_pow_mem_of_coprime {G : Type*} [Group G] (Z : Subgroup G)
    {x : G} {a b : ℕ} (hab : Nat.Coprime a b) (ha : x ^ a ∈ Z) (hb : x ^ b ∈ Z) :
    x ∈ Z := by
  obtain ⟨u, v, huv⟩ := hab.isCoprime
  have h1 : (a : ℤ) * u + (b : ℤ) * v = 1 := by
    rw [mul_comm (a : ℤ) u, mul_comm (b : ℤ) v]; exact huv
  have hx : x = (x ^ a) ^ u * (x ^ b) ^ v := by
    rw [← _root_.zpow_natCast x a, ← _root_.zpow_natCast x b, ← _root_.zpow_mul,
      ← _root_.zpow_mul, ← _root_.zpow_add, h1, zpow_one]
  rw [hx]
  exact Z.mul_mem (Z.zpow_mem ha u) (Z.zpow_mem hb v)

theorem mennickeZ_eq_top_of_coprime_of_lemma21 {m : ℕ} (hmq : Nat.Coprime m q)
    (h21 : MennickeLemma21 q m hmq) (hcop : Nat.Coprime m (q ^ 2 - 1)) :
    mennickeZ q m hmq = ⊤ := by
  have hAm : (slToAway q mennickeA) ^ m ∈ mennickeZ q m hmq :=
    mennickeA_pow_mem_mennickeZ q hmq
  have hAq : (slToAway q mennickeA) ^ (q ^ 2 - 1) ∈ mennickeZ q m hmq :=
    mennickeA_pow_q_sq_sub_one_mem_of_mennickeU_mem q (mennickeZ q m hmq) h21
  have hA : slToAway q mennickeA ∈ mennickeZ q m hmq :=
    mem_of_pow_mem_of_pow_mem_of_coprime (mennickeZ q m hmq) hcop hAm hAq
  exact eq_top_of_normal_of_mennickeA_mem q (mennickeZ q m hmq) hA

theorem mennickeZ_eq_top_of_coprime {m : ℕ} (hmq : Nat.Coprime m q)
    (hcop : Nat.Coprime m (q ^ 2 - 1)) :
    mennickeZ q m hmq = ⊤ :=
  mennickeZ_eq_top_of_coprime_of_lemma21 q hmq (Ihara.mennickeLemma21 q m hmq) hcop

end Centrality

section StemDescent

theorem ker_le_of_stem {G F : Type u} [Group G] [Group F] (red : G →* F)
    (hsurj : Function.Surjective red)
    (Q : Subgroup G) [Q.Normal] (hQker : Q ≤ red.ker)
    (hcen : ∀ g X : G, X ∈ red.ker → ⁅g, X⁆ ∈ Q)
    (hcomm : red.ker ≤ _root_.commutator G ⊔ Q)
    (hstem : HasTrivialSchurMultiplier F) :
    red.ker ≤ Q := by
  set f : G ⧸ Q →* F := QuotientGroup.lift Q red hQker with hfdef
  have hf_mk : ∀ g : G, f (QuotientGroup.mk g) = red g := fun g => rfl
  have hker_iff : ∀ g : G, (QuotientGroup.mk g : G ⧸ Q) ∈ f.ker ↔ g ∈ red.ker := by
    intro g; rw [MonoidHom.mem_ker, hf_mk, MonoidHom.mem_ker]
  have hfsurj : Function.Surjective f := by
    intro Y; obtain ⟨g, hg⟩ := hsurj Y
    exact ⟨QuotientGroup.mk g, by rw [hf_mk]; exact hg⟩
  have hfcen : f.ker ≤ Subgroup.center (G ⧸ Q) := by
    intro k hk
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q k
    rw [QuotientGroup.mk'_apply] at hk
    have hxN : x ∈ red.ker := (hker_iff x).mp hk
    rw [Subgroup.mem_center_iff]; intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q z
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hcomm_elt : ⁅g⁻¹, x⁻¹⁆ ∈ Q := hcen g⁻¹ x⁻¹ (red.ker.inv_mem hxN)
    have hco : (g * x)⁻¹ * (x * g) = ⁅g⁻¹, x⁻¹⁆⁻¹ := by
      simp only [commutatorElement_def, _root_.mul_inv_rev, inv_inv]; group
    rw [hco]; exact Q.inv_mem hcomm_elt
  have hfcomm : f.ker ≤ _root_.commutator (G ⧸ Q) := by
    intro k hk
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q k
    rw [QuotientGroup.mk'_apply] at hk ⊢
    have hxN : x ∈ red.ker := (hker_iff x).mp hk
    have hx_mem : x ∈ ((_root_.commutator G ⊔ Q : Subgroup G) : Set G) := hcomm hxN
    rw [Subgroup.mul_normal (_root_.commutator G) Q] at hx_mem
    obtain ⟨c, hc, w, hw, hcw⟩ := Set.mem_mul.mp hx_mem
    have hmkw : (QuotientGroup.mk w : G ⧸ Q) = 1 := (QuotientGroup.eq_one_iff w).mpr hw
    have hmkx : (QuotientGroup.mk x : G ⧸ Q) = QuotientGroup.mk c := by
      rw [← hcw, QuotientGroup.mk_mul, hmkw, mul_one]
    rw [hmkx]
    have hmaple : Subgroup.map (QuotientGroup.mk' Q) (_root_.commutator G)
        ≤ _root_.commutator (G ⧸ Q) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    have hcmem : QuotientGroup.mk' Q c ∈ Subgroup.map (QuotientGroup.mk' Q)
        (_root_.commutator G) := Subgroup.mem_map_of_mem _ hc
    rw [QuotientGroup.mk'_apply] at hcmem
    exact hmaple hcmem
  have hker_bot : f.ker = ⊥ := hstem (G ⧸ Q) f hfsurj hfcen hfcomm
  intro x hx
  have hxker : (QuotientGroup.mk x : G ⧸ Q) ∈ f.ker := (hker_iff x).mpr hx
  rw [hker_bot, Subgroup.mem_bot] at hxker
  exact (QuotientGroup.eq_one_iff x).mp hxker

end StemDescent

variable (q m : ℕ)

theorem mennickeCSP_of_centrality_of_stem (hmq : Nat.Coprime m q)
    (hcen : ∀ g X : SL(2, ZAway q), X ∈ principalCongruenceAway m q hmq → ⁅g, X⁆ ∈ mennickeQ q m)
    (hhabel : principalCongruenceAway m q hmq
      ≤ _root_.commutator (SL(2, ZAway q)) ⊔ mennickeQ q m)
    (hsurj : Function.Surjective (slAwayReduction m q hmq))
    (hstem : HasTrivialSchurMultiplier (SL(2, ZMod m))) : MennickeCSP m q hmq := by
  rw [mennickeCSP_iff_ker_le]
  exact ker_le_of_stem (slAwayReduction m q hmq) hsurj (mennickeQ q m)
    (normalClosure_le_principalCongruenceAway m q hmq) hcen hhabel hstem

theorem mennickeCSP_of_mennickeZ_eq_top_of_stem [NeZero q] (hmq : Nat.Coprime m q)
    (hZ : mennickeZ q m hmq = ⊤)
    (hhabel : principalCongruenceAway m q hmq
      ≤ _root_.commutator (SL(2, ZAway q)) ⊔ mennickeQ q m)
    (hsurj : Function.Surjective (slAwayReduction m q hmq))
    (hstem : HasTrivialSchurMultiplier (SL(2, ZMod m))) : MennickeCSP m q hmq := by
  refine mennickeCSP_of_centrality_of_stem q m hmq ?_ hhabel hsurj hstem
  intro g X hX
  have hg : g ∈ mennickeZ q m hmq := hZ ▸ Subgroup.mem_top g
  exact (mem_mennickeZ_iff q m hmq g).mp hg X hX

end SolH7a
p2m_reactivate "P2MW.S_Ihara_mennickeCSP_of_coprime_of_stem.SolH7a"

open scoped MatrixGroups

theorem solution (q m : ℕ) [NeZero q] (hmq : Nat.Coprime m q) (hcop : Nat.Coprime m (q ^ 2 - 1))
    (hhabel : Ihara.principalCongruenceAway m q hmq
      ≤ _root_.commutator (SL(2, Ihara.ZAway q)) ⊔ Ihara.mennickeQ q m)
    (hsurj : Function.Surjective (Ihara.slAwayReduction m q hmq))
    (hstem : Ihara.HasTrivialSchurMultiplier (SL(2, ZMod m))) : Ihara.MennickeCSP m q hmq :=
  SolH7a.mennickeCSP_of_mennickeZ_eq_top_of_stem q m hmq
    (SolH7a.mennickeZ_eq_top_of_coprime q hmq hcop) hhabel hsurj hstem

#print axioms solution

end S_Ihara_mennickeCSP_of_coprime_of_stem
end P2MW
export P2MW.S_Ihara_mennickeCSP_of_coprime_of_stem (solution)
