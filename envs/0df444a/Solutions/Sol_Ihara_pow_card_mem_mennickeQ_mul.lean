-- Prove2me | solution 1 for Ihara.pow_card_mem_mennickeQ_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/45db7d25-972a-55dc-a630-a2007efb2861

import Definitions.Def_SchurMultiplierTrivial
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Abelianization.Defs
import Definitions.Def_IharaMennickeCarrier
import Theorems.Thm_Ihara_mennickeQ_le_commutator_sup_mennickeQ_mul
import Theorems.Thm_Ihara_mennickeLemma21
import Theorems.Thm_Ihara_normalClosure_mennickeA_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_pow_card_mem_mennickeQ_mul

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff MennickeCSP normalClosure_le_principalCongruenceAway qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ mem_mennickeZ_iff MennickeLemma21 mennickeLemma21_iff ZAway slToAway coe_slToAway zAwayToZMod zAwayToZMod_algebraMap mennickeQ_le_commutator_sup_mennickeQ_mul mennickeLemma21 normalClosure_mennickeA_eq_top"
p2m_open "Ihara"

open Matrix
open scoped MatrixGroups

section Remint

private theorem sl2coe_mul_h7b {R : Type*} [CommRing R] (A B : SL(2, R)) :
    ((A * B : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) * B := rfl
private theorem sl2coe_one_h7b {R : Type*} [CommRing R] :
    ((1 : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = 1 := rfl
private theorem sl2coe_pow_h7b {R : Type*} [CommRing R] (A : SL(2, R)) (n : ℕ) :
    ((A ^ n : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) ^ n := rfl

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
  rw [sl2coe_mul_h7b, sl2coe_mul_h7b,
    slToAway_mennickeA_pow_coe, slToAway_mennickeA_coe, mennickeU_coe,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qInv_mul_natCast_q_sq q]

theorem mennickeU_inv_mul_mennickeA_mul_mennickeU :
    (mennickeU q)⁻¹ * slToAway q mennickeA * mennickeU q =
      (slToAway q mennickeA) ^ (q ^ 2) := by
  rw [mul_assoc, ← mennickeU_mul_mennickeA_pow_sq q, ← mul_assoc, inv_mul_cancel, one_mul]

variable [NeZero q]

scoped instance mennickeZ_normal {m : ℕ} (hmq : Nat.Coprime m q) : (mennickeZ q m hmq).Normal := by
  haveI hmap : (Subgroup.map (QuotientGroup.mk' (mennickeQ q m))
      (principalCongruenceAway m q hmq)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rw [mennickeZ]
  exact Subgroup.Normal.comap inferInstance _

theorem normalClosure_mennickeA_pow_one_eq_top :
    Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ 1} : Set SL(2, ZAway q)) = ⊤ := by
  rw [pow_one]; exact normalClosure_mennickeA_eq_top q

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

theorem normalClosure_q_sq_sub_one_le_mennickeZ_of_lemma21 {m : ℕ} (hmq : Nat.Coprime m q)
    (h21 : MennickeLemma21 q m hmq) :
    Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ (q ^ 2 - 1)} : Set SL(2, ZAway q)) ≤
      mennickeZ q m hmq :=
  Subgroup.normalClosure_le_normal
    (Set.singleton_subset_iff.mpr
      (mennickeA_pow_q_sq_sub_one_mem_of_mennickeU_mem q (mennickeZ q m hmq) h21))

omit [NeZero q] in
theorem two_dvd_sq_sub_one_of_not_dvd {q : ℕ} (hq : ¬ 2 ∣ q) : 2 ∣ q ^ 2 - 1 := by
  obtain ⟨k, hk⟩ : ∃ k, q = 2 * k + 1 := ⟨q / 2, by omega⟩
  refine ⟨2 * (k * k) + 2 * k, ?_⟩
  have hq2 : q ^ 2 = 2 * (2 * (k * k) + 2 * k) + 1 := by rw [hk]; ring
  rw [hq2, Nat.add_sub_cancel]

omit [NeZero q] in
theorem three_dvd_sq_sub_one_of_not_dvd {q : ℕ} (hq : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  obtain ⟨k, hk⟩ : ∃ k, q = 3 * k + 1 ∨ q = 3 * k + 2 := ⟨q / 3, by omega⟩
  rcases hk with h | h
  · refine ⟨3 * (k * k) + 2 * k, ?_⟩
    have hq2 : q ^ 2 = 3 * (3 * (k * k) + 2 * k) + 1 := by rw [h]; ring
    rw [hq2, Nat.add_sub_cancel]
  · refine ⟨3 * (k * k) + 4 * k + 1, ?_⟩
    have hq2 : q ^ 2 = 3 * (3 * (k * k) + 4 * k + 1) + 1 := by rw [h]; ring
    rw [hq2, Nat.add_sub_cancel]

omit [NeZero q] in
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

omit [NeZero q] in
theorem mennickeQ_le_of_dvd (a b : ℕ) (hdvd : a ∣ b) : mennickeQ q b ≤ mennickeQ q a := by
  apply Subgroup.normalClosure_le_normal
  rw [Set.singleton_subset_iff]
  obtain ⟨c, rfl⟩ := hdvd
  rw [pow_mul]
  exact pow_mem (Subgroup.subset_normalClosure (Set.mem_singleton _)) c

theorem mennickeQ_le_mennickeZ_of_dvd (m m'' : ℕ) (hmq : Nat.Coprime m q)
    (hdvd : (q ^ 2 - 1) ∣ m'') : mennickeQ q m'' ≤ mennickeZ q m hmq :=
  le_trans (mennickeQ_le_of_dvd q (q ^ 2 - 1) m'' hdvd)
    (normalClosure_q_sq_sub_one_le_mennickeZ_of_lemma21 q hmq (mennickeLemma21 q m hmq))

omit [NeZero q] in
theorem castHom_comp_zAwayToZMod {M N : ℕ} (hMq : Nat.Coprime M q) (hNq : Nat.Coprime N q)
    (hNM : N ∣ M) :
    (ZMod.castHom hNM (ZMod N)).comp (zAwayToZMod M q hMq) = zAwayToZMod N q hNq := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (q : ℤ)) ?_
  ext a
  simp only [RingHom.comp_apply, zAwayToZMod_algebraMap, map_intCast]

theorem zmod_eq_of_castHom_eq {m' m'' : ℕ} [NeZero m'] [NeZero m''] (hcop : Nat.Coprime m' m'')
    {x y : ZMod (m' * m'')}
    (h1 : ZMod.castHom (dvd_mul_right m' m'') (ZMod m') x
        = ZMod.castHom (dvd_mul_right m' m'') (ZMod m') y)
    (h2 : ZMod.castHom (dvd_mul_left m'' m') (ZMod m'') x
        = ZMod.castHom (dvd_mul_left m'' m') (ZMod m'') y) :
    x = y := by
  haveI : NeZero (m' * m'') := ⟨Nat.mul_ne_zero (NeZero.ne m') (NeZero.ne m'')⟩
  rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y] at h1 h2 ⊢
  rw [map_natCast, map_natCast, ZMod.natCast_eq_natCast_iff] at h1 h2
  rw [ZMod.natCast_eq_natCast_iff]
  exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, h2⟩

omit [NeZero q] in
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
  exact (DFunLike.congr_fun (castHom_comp_zAwayToZMod q hmq hm'q hdvd)
    (((x : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) i j)).symm

omit [NeZero q] in
theorem principalCongruenceAway_mul_eq_inf (m' m'' : ℕ) [NeZero m'] [NeZero m'']
    (hcop : Nat.Coprime m' m'') (hm'q : Nat.Coprime m' q) (hm''q : Nat.Coprime m'' q)
    (hmq : Nat.Coprime (m' * m'') q) :
    principalCongruenceAway (m' * m'') q hmq =
      principalCongruenceAway m' q hm'q ⊓ principalCongruenceAway m'' q hm''q := by
  refine le_antisymm (le_inf ?_ ?_) ?_
  · intro x hx
    rw [mem_principalCongruenceAway_iff] at hx ⊢
    rw [slAwayReduction_eq_map_castHom q (m' * m'') m' (dvd_mul_right m' m'') hmq hm'q, hx,
      map_one]
  · intro x hx
    rw [mem_principalCongruenceAway_iff] at hx ⊢
    rw [slAwayReduction_eq_map_castHom q (m' * m'') m'' (dvd_mul_left m'' m') hmq hm''q, hx,
      map_one]
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [mem_principalCongruenceAway_iff] at hx1 hx2 ⊢
    have key1 : Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_right m' m'') (ZMod m'))
        (slAwayReduction (m' * m'') q hmq x) =
        Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_right m' m'') (ZMod m'))
          (1 : SL(2, ZMod (m' * m''))) := by
      rw [map_one,
        ← slAwayReduction_eq_map_castHom q (m' * m'') m' (dvd_mul_right m' m'') hmq hm'q]
      exact hx1
    have key2 : Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_left m'' m') (ZMod m''))
        (slAwayReduction (m' * m'') q hmq x) =
        Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_mul_left m'' m') (ZMod m''))
          (1 : SL(2, ZMod (m' * m''))) := by
      rw [map_one,
        ← slAwayReduction_eq_map_castHom q (m' * m'') m'' (dvd_mul_left m'' m') hmq hm''q]
      exact hx2
    refine Subtype.ext ?_
    ext i j
    refine zmod_eq_of_castHom_eq hcop ?_ ?_
    · exact congrFun (congrFun (congrArg Subtype.val key1) i) j
    · exact congrFun (congrFun (congrArg Subtype.val key2) i) j

end Remint

end Ihara
p2m_reactivate "P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.Ihara"

section Inl_A3_EllStem

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff MennickeCSP normalClosure_le_principalCongruenceAway qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ mem_mennickeZ_iff MennickeLemma21 mennickeLemma21_iff ZAway slToAway coe_slToAway zAwayToZMod zAwayToZMod_algebraMap mennickeQ_le_commutator_sup_mennickeQ_mul mennickeLemma21 normalClosure_mennickeA_eq_top"
p2m_open "Ihara"

open Subgroup

open scoped commutatorElement

universe u

section Central

variable {E : Type*} [Group E]

theorem commutatorElement_mul_left_of_mem_center {a b z : E} (hz : z ∈ center E) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hz' := mem_center_iff.mp hz
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_assoc a z b, ← hz' b,
    ← mul_assoc, ← mul_assoc, mul_inv_cancel_right]

theorem commutatorElement_mul_right_of_mem_center {a b z : E} (hz : z ∈ center E) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv, commutatorElement_mul_left_of_mem_center hz, commutatorElement_inv]

theorem commutator_eq_of_mul_center (X : Subgroup E)
    (hX : ∀ e : E, ∃ c ∈ X, ∃ z ∈ center E, e = c * z) : commutator E = ⁅X, X⁆ := by
  refine le_antisymm ?_ (commutator_mono le_top le_top)
  rw [commutator_def, commutator_le]
  rintro a - b -
  obtain ⟨c, hc, z, hz, rfl⟩ := hX a
  obtain ⟨d, hd, w, hw, rfl⟩ := hX b
  rw [commutatorElement_mul_left_of_mem_center hz, commutatorElement_mul_right_of_mem_center hw]
  exact commutator_mem_commutator hc hd

end Central
p2m_reactivate "P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.Ihara"

section PerfectStem

variable {F E : Type u} [Group F] [Group E]

theorem eq_one_of_perfect_of_hasTrivialSchurMultiplier (hperf : commutator F = ⊤)
    (hstem : HasTrivialSchurMultiplier F) (π : E →* F) (hsurj : Function.Surjective π)
    (hcent : π.ker ≤ center E) {x : E} (hx : x ∈ π.ker) (hxc : x ∈ commutator E) : x = 1 := by
  set X : Subgroup E := commutator E with hXdef

  have hXmap : X.map π = ⊤ := by
    rw [hXdef, map_commutator_eq, MonoidHom.range_eq_top.mpr hsurj, ← commutator_def, hperf]

  have hdec : ∀ e : E, ∃ c ∈ X, ∃ z ∈ center E, e = c * z := by
    intro e
    have he : π e ∈ X.map π := by rw [hXmap]; exact mem_top _
    obtain ⟨c, hc, hce⟩ := he
    refine ⟨c, hc, c⁻¹ * e, hcent ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hce, inv_mul_cancel]

  have hXX : ⁅X, X⁆ = X := (commutator_eq_of_mul_center X hdec).symm

  set π' : X →* F := π.comp X.subtype with hπ'
  have hsurj' : Function.Surjective π' := by
    intro f
    have hf : f ∈ X.map π := by rw [hXmap]; exact mem_top _
    obtain ⟨c, hc, rfl⟩ := hf
    exact ⟨⟨c, hc⟩, rfl⟩
  have hcent' : π'.ker ≤ center X := by
    intro y hy
    rw [mem_center_iff]
    intro g
    have hyc : (y : E) ∈ center E := hcent (by simpa [hπ'] using hy)
    exact Subtype.ext ((mem_center_iff.mp hyc) g)
  have hcomm' : π'.ker ≤ commutator X := by
    intro y _
    have hy : (y : E) ∈ ⁅X, X⁆ := by rw [hXX]; exact y.2
    rw [← map_subtype_commutator] at hy
    obtain ⟨y', hy', hyy⟩ := hy
    rwa [← Subtype.coe_injective hyy]
  have hker : π'.ker = ⊥ := hstem X π' hsurj' hcent' hcomm'

  have hx' : (⟨x, hxc⟩ : X) ∈ π'.ker := by simpa [hπ'] using hx
  rw [hker, mem_bot] at hx'
  exact congrArg Subtype.val hx'

end PerfectStem
p2m_reactivate "P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.Ihara"

section Product

variable {F₁ F₂ E : Type u} [Group F₁] [Group F₂] [Group E]

def fstPreimage (π : E →* F₁ × F₂) : Subgroup E := ((MonoidHom.snd F₁ F₂).comp π).ker

def sndPreimage (π : E →* F₁ × F₂) : Subgroup E := ((MonoidHom.fst F₁ F₂).comp π).ker

theorem mem_fstPreimage {π : E →* F₁ × F₂} {e : E} : e ∈ fstPreimage π ↔ (π e).2 = 1 := Iff.rfl

theorem mem_sndPreimage {π : E →* F₁ × F₂} {e : E} : e ∈ sndPreimage π ↔ (π e).1 = 1 := Iff.rfl

variable (π : E →* F₁ × F₂) (hsurj : Function.Surjective π) (hcent : π.ker ≤ center E)

include hsurj in
theorem map_fstPreimage : (fstPreimage π).map π = (⊤ : Subgroup F₁).prod ⊥ := by
  ext ⟨f₁, f₂⟩
  simp only [mem_map, mem_fstPreimage, mem_prod, mem_top, mem_bot, true_and]
  constructor
  · rintro ⟨e, he, hef⟩
    rw [hef] at he
    exact he
  · rintro rfl
    obtain ⟨e, he⟩ := hsurj (f₁, 1)
    exact ⟨e, by rw [he], he⟩

include hsurj in
theorem map_sndPreimage : (sndPreimage π).map π = (⊥ : Subgroup F₁).prod ⊤ := by
  ext ⟨f₁, f₂⟩
  simp only [mem_map, mem_sndPreimage, mem_prod, mem_top, mem_bot, and_true]
  constructor
  · rintro ⟨e, he, hef⟩
    rw [hef] at he
    exact he
  · rintro rfl
    obtain ⟨e, he⟩ := hsurj (1, f₂)
    exact ⟨e, by rw [he], he⟩

include hcent in

theorem commutator_fst_snd_le_center : ⁅fstPreimage π, sndPreimage π⁆ ≤ center E := by
  refine le_trans ?_ hcent
  rw [commutator_le]
  intro a ha b hb
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def]
  rw [mem_fstPreimage] at ha
  rw [mem_sndPreimage] at hb
  ext
  · simp [hb]
  · simp [ha]

include hsurj hcent in

theorem commutator_fst_snd_eq_bot (hperf : commutator F₁ = ⊤) :
    ⁅fstPreimage π, sndPreimage π⁆ = ⊥ := by
  set H₁ := fstPreimage π
  set H₂ := sndPreimage π
  have hc : ⁅H₁, H₂⁆ ≤ center E := commutator_fst_snd_le_center π hcent

  have h3 : ⁅⁅H₁, H₁⁆, H₂⁆ = ⊥ := by
    refine commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [commutator_eq_bot_iff_le_centralizer]
      exact le_trans hc (center_le_centralizer _)
    · rw [commutator_eq_bot_iff_le_centralizer, commutator_comm]
      exact le_trans hc (center_le_centralizer _)

  have hmap : (⁅H₁, H₁⁆ : Subgroup E).map π = (⊤ : Subgroup F₁).prod ⊥ := by
    rw [map_commutator, map_fstPreimage π hsurj, commutator_prod_prod, ← commutator_def, hperf,
      commutator_bot_left]
  rw [eq_bot_iff, commutator_le]
  intro a ha b hb
  have ha' : π a ∈ (⁅H₁, H₁⁆ : Subgroup E).map π := by
    rw [hmap, mem_prod]; exact ⟨mem_top _, ha⟩
  obtain ⟨c, hc1, hca⟩ := ha'
  have hz : c⁻¹ * a ∈ center E := hcent (by rw [MonoidHom.mem_ker, map_mul, map_inv, hca,
    inv_mul_cancel])
  have : a = c * (c⁻¹ * a) := by group
  rw [this, commutatorElement_mul_left_of_mem_center hz, ← h3]
  exact commutator_mem_commutator hc1 hb

include hsurj hcent in
theorem commute_of_perfect_fst (hperf : commutator F₁ = ⊤) {a b : E} (ha : (π a).2 = 1)
    (hb : (π b).1 = 1) : Commute a b := by
  have h := commutator_fst_snd_eq_bot π hsurj hcent hperf
  rw [eq_bot_iff, commutator_le] at h
  exact (commutatorElement_eq_one_iff_commute).mp ((mem_bot).mp (h a ha b hb))

include hsurj hcent in

theorem pow_eq_one_of_prod (hperf : commutator F₁ = ⊤) (hstem : HasTrivialSchurMultiplier F₁)
    {n : ℕ}
    (hF₂ : ∀ (E' : Type u) [Group E'] (π' : E' →* F₂), Function.Surjective π' →
      π'.ker ≤ center E' → ∀ y ∈ π'.ker, y ∈ commutator E' → y ^ n = 1)
    {x : E} (hx : x ∈ π.ker) (hxc : x ∈ commutator E) : x ^ n = 1 := by
  set H₁ := fstPreimage π
  set H₂ := sndPreimage π

  have hcomm : ∀ (a : H₁) (b : H₂), Commute ((H₁.subtype) a) ((H₂.subtype) b) :=
    fun a b => commute_of_perfect_fst π hsurj hcent hperf a.2 b.2
  set μ : H₁ × H₂ →* E := MonoidHom.noncommCoprod H₁.subtype H₂.subtype hcomm with hμ
  have hμsurj : Function.Surjective μ := by
    intro e
    obtain ⟨a, ha⟩ := hsurj ((π e).1, 1)
    have ha1 : a ∈ H₁ := by rw [mem_fstPreimage, ha]
    have hb2 : a⁻¹ * e ∈ H₂ := by
      rw [mem_sndPreimage, map_mul, map_inv, ha, Prod.fst_mul, Prod.fst_inv, inv_mul_cancel]
    exact ⟨(⟨a, ha1⟩, ⟨a⁻¹ * e, hb2⟩), by simp [hμ]⟩

  have hxμ : x ∈ (commutator (H₁ × H₂)).map μ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hμsurj, ← commutator_def]; exact hxc
  rw [commutator_def, ← top_prod_top, commutator_prod_prod] at hxμ
  obtain ⟨⟨c₁, c₂⟩, ⟨hc₁, hc₂⟩, hcx⟩ := hxμ
  simp only [hμ, MonoidHom.noncommCoprod_apply, coe_subtype] at hcx

  have hπx : π x = 1 := hx
  have hπc₁2 : (π c₁).2 = 1 := c₁.2
  have hπc₂1 : (π c₂).1 = 1 := c₂.2
  have hπc₁ : π (c₁ : E) = 1 := by
    have h1 : (π c₁).1 * (π c₂).1 = 1 := by
      rw [← Prod.fst_mul, ← map_mul, hcx, hπx, Prod.fst_one]
    rw [hπc₂1, mul_one] at h1
    exact Prod.ext h1 hπc₁2
  have hπc₂ : π (c₂ : E) = 1 := by
    have h := congrArg π hcx
    rwa [map_mul, hπc₁, one_mul, hπx] at h

  set π₁ : H₁ →* F₁ := (MonoidHom.fst F₁ F₂).comp (π.comp H₁.subtype) with hπ₁
  have hsurj₁ : Function.Surjective π₁ := by
    intro f
    obtain ⟨a, ha⟩ := hsurj (f, 1)
    exact ⟨⟨a, by rw [mem_fstPreimage, ha]⟩, by simp [hπ₁, ha]⟩
  have hker₁ : ∀ y : H₁, y ∈ π₁.ker → (y : E) ∈ π.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    exact Prod.ext hy y.2
  have hcent₁ : π₁.ker ≤ center H₁ := by
    intro y hy
    rw [mem_center_iff]
    intro g
    exact Subtype.ext ((mem_center_iff.mp (hcent (hker₁ y hy))) g)
  have hc₁one : c₁ = 1 :=
    eq_one_of_perfect_of_hasTrivialSchurMultiplier hperf hstem π₁ hsurj₁ hcent₁
      (by rw [MonoidHom.mem_ker]; simp [hπ₁, hπc₁]) (by rw [← commutator_def] at hc₁; exact hc₁)

  set π₂ : H₂ →* F₂ := (MonoidHom.snd F₁ F₂).comp (π.comp H₂.subtype) with hπ₂
  have hsurj₂ : Function.Surjective π₂ := by
    intro f
    obtain ⟨a, ha⟩ := hsurj (1, f)
    exact ⟨⟨a, by rw [mem_sndPreimage, ha]⟩, by simp [hπ₂, ha]⟩
  have hker₂ : ∀ y : H₂, y ∈ π₂.ker → (y : E) ∈ π.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    exact Prod.ext y.2 hy
  have hcent₂ : π₂.ker ≤ center H₂ := by
    intro y hy
    rw [mem_center_iff]
    intro g
    exact Subtype.ext ((mem_center_iff.mp (hcent (hker₂ y hy))) g)
  have hc₂n : c₂ ^ n = 1 :=
    hF₂ H₂ π₂ hsurj₂ hcent₂ c₂ (by rw [MonoidHom.mem_ker]; simp [hπ₂, hπc₂])
      (by rw [← commutator_def] at hc₂; exact hc₂)

  rw [← hcx, hc₁one, OneMemClass.coe_one, one_mul, ← SubgroupClass.coe_pow, hc₂n,
    OneMemClass.coe_one]

include hsurj hcent in

theorem ker_eq_bot_of_prod_of_perfect (hperf₁ : commutator F₁ = ⊤)
    (hstem₁ : HasTrivialSchurMultiplier F₁) (hperf₂ : commutator F₂ = ⊤)
    (hstem₂ : HasTrivialSchurMultiplier F₂) (hcomm : π.ker ≤ commutator E) : π.ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ^ 1 = 1 :=
    pow_eq_one_of_prod π hsurj hcent hperf₁ hstem₁ (n := 1)
      (fun E' _ π' hs hc y hy hyc => by
        rw [pow_one]
        exact eq_one_of_perfect_of_hasTrivialSchurMultiplier hperf₂ hstem₂ π' hs hc hy hyc)
      hx (hcomm hx)
  rwa [pow_one, ← mem_bot] at h1

end Product
p2m_reactivate "P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.Ihara"

theorem commutator_prod_eq_top {F₁ F₂ : Type*} [Group F₁] [Group F₂] (h₁ : commutator F₁ = ⊤)
    (h₂ : commutator F₂ = ⊤) : commutator (F₁ × F₂) = ⊤ := by
  rw [commutator_def, ← top_prod_top, commutator_prod_prod, ← commutator_def, ← commutator_def, h₁,
    h₂]

theorem hasTrivialSchurMultiplier_prod_of_perfect {F₁ F₂ : Type u} [Group F₁] [Group F₂]
    (hperf₁ : commutator F₁ = ⊤) (hstem₁ : HasTrivialSchurMultiplier F₁)
    (hperf₂ : commutator F₂ = ⊤) (hstem₂ : HasTrivialSchurMultiplier F₂) :
    HasTrivialSchurMultiplier (F₁ × F₂) := by
  intro E _ π hsurj hcent hcomm
  exact ker_eq_bot_of_prod_of_perfect π hsurj hcent hperf₁ hstem₁ hperf₂ hstem₂ hcomm

theorem commutator_eq_top_of_mulEquiv {G H : Type*} [Group G] [Group H] (h : commutator H = ⊤)
    (e : G ≃* H) : commutator G = ⊤ := by
  have := congrArg (Subgroup.map e.symm.toMonoidHom) h
  rwa [map_commutator_eq, MonoidHom.range_eq_top.mpr e.symm.surjective, ← commutator_def,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr e.symm.surjective] at this

end Ihara
p2m_reactivate "P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.Ihara"

end Inl_A3_EllStem
p2m_reactivate "P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.Ihara"

section Inl_A3_SL2ZModFacts

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff MennickeCSP normalClosure_le_principalCongruenceAway qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ mem_mennickeZ_iff MennickeLemma21 mennickeLemma21_iff ZAway slToAway coe_slToAway zAwayToZMod zAwayToZMod_algebraMap mennickeQ_le_commutator_sup_mennickeQ_mul mennickeLemma21 normalClosure_mennickeA_eq_top"
p2m_open "Ihara"

open Matrix Polynomial

open scoped MatrixGroups

section CRT

variable (R S : Type*) [CommRing R] [CommRing S]

def slProdEquiv : SL(2, R × S) ≃* SL(2, R) × SL(2, S) where
  toFun := (SpecialLinearGroup.map (RingHom.fst R S)).prod (SpecialLinearGroup.map (RingHom.snd R S))
  invFun gh :=
    ⟨of fun i j => (((gh.1 : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) i j,
        ((gh.2 : SL(2, S)) : Matrix (Fin 2) (Fin 2) S) i j), by
      have h1 := gh.1.prop
      have h2 := gh.2.prop
      rw [det_fin_two] at h1 h2 ⊢
      exact Prod.ext (by simpa using h1) (by simpa using h2)⟩
  left_inv g := Subtype.ext <| Matrix.ext fun _ _ => rfl
  right_inv gh := Prod.ext (Subtype.ext <| Matrix.ext fun _ _ => rfl)
    (Subtype.ext <| Matrix.ext fun _ _ => rfl)
  map_mul' := map_mul _

variable {R S} in

def slCongr (e : R ≃+* S) : SL(2, R) ≃* SL(2, S) where
  toFun := SpecialLinearGroup.map e.toRingHom
  invFun := SpecialLinearGroup.map e.symm.toRingHom
  left_inv _ := Subtype.ext <| Matrix.ext fun _ _ => e.symm_apply_apply _
  right_inv _ := Subtype.ext <| Matrix.ext fun _ _ => e.apply_symm_apply _
  map_mul' := map_mul _

noncomputable def slZModMulEquiv {a b : ℕ} (h : Nat.Coprime a b) :
    SL(2, ZMod (a * b)) ≃* SL(2, ZMod a) × SL(2, ZMod b) :=
  (slCongr (ZMod.chineseRemainder h)).trans (slProdEquiv (ZMod a) (ZMod b))

end CRT
p2m_reactivate "P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.Ihara"

section SmallPrimes

variable {R : Type*} [CommRing R]

theorem sq_eq_trace_smul_sub_one (A : SL(2, R)) :
    (A : Matrix (Fin 2) (Fin 2) R) * A = (Matrix.trace (A : Matrix (Fin 2) (Fin 2) R)) • (A : Matrix (Fin 2) (Fin 2) R) - 1 := by
  have hdet := A.prop
  rw [det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    first
    | ring1
    | linear_combination (-1 : R) * hdet

theorem pow_twelve_eq_one_of_sq_eq {A : Matrix (Fin 2) (Fin 2) R} {t : R}
    (ht : t = 0 ∨ t = 1 ∨ t = -1) (hA : A * A = t • A - 1) : A ^ 12 = 1 := by
  rcases ht with rfl | rfl | rfl
  · rw [zero_smul, zero_sub] at hA
    rw [show 12 = 2 * 6 from rfl, pow_mul, sq, hA]
    exact Even.neg_one_pow ⟨3, rfl⟩
  · rw [one_smul] at hA
    have h3 : A ^ 3 = -1 := by
      rw [pow_succ, sq, hA, sub_mul, one_mul, hA]; abel
    rw [show 12 = 3 * 4 from rfl, pow_mul, h3]
    exact Even.neg_one_pow ⟨2, rfl⟩
  · rw [neg_smul, one_smul] at hA
    have h3 : A ^ 3 = 1 := by
      rw [pow_succ, sq, hA, sub_mul, neg_mul, one_mul, hA]; abel
    rw [show 12 = 3 * 4 from rfl, pow_mul, h3, one_pow]

theorem pow_twelve_eq_one_SL2_ZMod {p : ℕ} (hp : p = 2 ∨ p = 3) (A : SL(2, ZMod p)) :
    A ^ 12 = 1 := by
  apply Subtype.ext
  rw [sl2coe_pow_h7b, sl2coe_one_h7b]
  refine pow_twelve_eq_one_of_sq_eq ?_ (sq_eq_trace_smul_sub_one A)
  generalize Matrix.trace (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = t
  rcases hp with rfl | rfl
  · revert t; decide
  · revert t; decide

theorem pow_eq_one_of_map_castHom_eq_one {p n : ℕ} [Fact p.Prime] (hn : n ≠ 0)
    (H : SL(2, ZMod (p ^ n)))
    (hH : SpecialLinearGroup.map (ZMod.castHom (dvd_pow_self p hn) (ZMod p)) H = 1) :
    H ^ (p ^ (n - 1)) = 1 := by
  have hp : (p : ℕ).Prime := Fact.out
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero hn
  rw [Nat.add_sub_cancel]
  set 𝕄 := Matrix (Fin 2) (Fin 2) (ZMod (p ^ (k + 1)))

  have hentry : ∀ i j, ∃ c : ℕ, ((H : 𝕄) - 1) i j = (p : ZMod (p ^ (k + 1))) * c := by
    intro i j
    have hij := congrArg (fun M : SL(2, ZMod p) => (M : Matrix (Fin 2) (Fin 2) (ZMod p)) i j) hH
    simp only [SpecialLinearGroup.map, MonoidHom.coe_mk, OneHom.coe_mk, RingHom.mapMatrix_apply,
      Matrix.map_apply, sl2coe_one_h7b] at hij
    have h0 : ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p) (((H : 𝕄) - 1) i j) = 0 := by
      rw [Matrix.sub_apply, map_sub, hij, sub_eq_zero]
      rcases eq_or_ne i j with rfl | hne
      · simp
      · simp [Matrix.one_apply_ne hne]
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at h0
    obtain ⟨c, hc⟩ := h0
    refine ⟨c, ?_⟩
    rw [← ZMod.natCast_zmod_val (((H : 𝕄) - 1) i j), hc, Nat.cast_mul]
  choose X hX using hentry
  have hHX : (H : 𝕄) = 1 + (p : 𝕄) * of (fun i j => (X i j : ZMod (p ^ (k + 1)))) := by
    rw [← sub_eq_iff_eq_add', ← Matrix.diagonal_natCast]
    ext i j
    rw [hX i j, Matrix.diagonal_mul, of_apply]

  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ[X],
      (1 + C (p : ℤ) * Polynomial.X) ^ p ^ k - 1 = ((p ^ (k + 1) : ℕ) : ℤ[X]) * Q := by
    have h := dvd_sub_pow_of_dvd_sub (p := p) (a := 1 + C (p : ℤ) * Polynomial.X) (b := 1)
      ⟨C 1 * Polynomial.X, by simp⟩ k
    rw [one_pow] at h
    obtain ⟨Q, hQ⟩ := h
    exact ⟨Q, by rw [hQ]; norm_cast⟩

  set Xm : 𝕄 := of fun i j => (X i j : ZMod (p ^ (k + 1)))
  have heval := congrArg (Polynomial.aeval (R := ℤ) Xm) hQ
  simp only [map_sub, map_pow, map_add, map_one, map_mul, aeval_X, map_natCast] at heval

  have hzero : ((p ^ (k + 1) : ℕ) : 𝕄) = 0 := by
    rw [← map_natCast (algebraMap (ZMod (p ^ (k + 1))) 𝕄), ZMod.natCast_self, map_zero]
  rw [hzero, zero_mul, sub_eq_zero, ← hHX] at heval
  exact Subtype.ext (by rw [sl2coe_pow_h7b, heval, sl2coe_one_h7b])

theorem pow_twelve_mul_eq_one_SL2_ZMod_prime_pow {p : ℕ} (hp : p = 2 ∨ p = 3) (n : ℕ)
    (g : SL(2, ZMod (p ^ n))) : g ^ (12 * p ^ n) = 1 := by
  haveI : Fact p.Prime := ⟨by rcases hp with rfl | rfl; exacts [Nat.prime_two, Nat.prime_three]⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    haveI : Subsingleton (ZMod (p ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero p)
    exact Subtype.ext (Subsingleton.elim _ _)
  · have h12 : SpecialLinearGroup.map (ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p)) (g ^ 12) = 1 := by
      rw [map_pow, pow_twelve_eq_one_SL2_ZMod hp]
    have := pow_eq_one_of_map_castHom_eq_one hn.ne' (g ^ 12) h12
    rw [← pow_mul] at this
    rw [show 12 * p ^ n = 12 * p ^ (n - 1) * p by
      rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hn], pow_mul, this, one_pow]

theorem prime_dvd_card_SL2_ZMod_two_pow_mul_three_pow (a b : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hdvd : ℓ ∣ Nat.card (SL(2, ZMod (2 ^ a * 3 ^ b)))) : ℓ = 2 ∨ ℓ = 3 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero (2 ^ a * 3 ^ b) := ⟨by positivity⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd

  have hcop : Nat.Coprime (2 ^ a) (3 ^ b) := by
    exact Nat.Coprime.pow _ _ (by norm_num)
  set e := slZModMulEquiv hcop
  have h1 : (e x).1 ^ (12 * 2 ^ a) = 1 := pow_twelve_mul_eq_one_SL2_ZMod_prime_pow (Or.inl rfl) a _
  have h2 : (e x).2 ^ (12 * 3 ^ b) = 1 := pow_twelve_mul_eq_one_SL2_ZMod_prime_pow (Or.inr rfl) b _
  have hex : e x ^ (12 * 2 ^ a * (12 * 3 ^ b)) = 1 := by
    refine Prod.ext ?_ ?_
    · rw [Prod.pow_fst, pow_mul, h1, one_pow, Prod.fst_one]
    · rw [Prod.pow_snd, pow_mul', h2, one_pow, Prod.snd_one]
  have hx' : x ^ (12 * 2 ^ a * (12 * 3 ^ b)) = 1 := by
    apply e.injective
    rw [map_pow, hex, map_one]
  have hord : ℓ ∣ 12 * 2 ^ a * (12 * 3 ^ b) := by
    rw [← hx]; exact orderOf_dvd_of_pow_eq_one hx'

  have h23 : ∀ {u : ℕ}, ℓ ∣ 12 * u → ℓ ∣ u ∨ ℓ = 2 ∨ ℓ = 3 := by
    intro u hu
    rcases (Nat.Prime.dvd_mul hℓ).mp hu with h | h
    · have h12 : ℓ ∣ 2 ^ 2 * 3 := by norm_num at h ⊢; exact h
      rcases (Nat.Prime.dvd_mul hℓ).mp h12 with h | h
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp
          (hℓ.dvd_of_dvd_pow h)))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp h))
    · exact Or.inl h
  rcases (Nat.Prime.dvd_mul hℓ).mp hord with h | h
  · rcases h23 h with h | h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow h))
    · exact Or.inl h
    · exact Or.inr h
  · rcases h23 h with h | h | h
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp (hℓ.dvd_of_dvd_pow h))
    · exact Or.inl h
    · exact Or.inr h

end SmallPrimes
p2m_reactivate "P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.Ihara"

section LargePrimes

theorem commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod
    (hP1 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 → commutator (SL(2, ZMod (p ^ n))) = ⊤)
    (hP2 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 → HasTrivialSchurMultiplier (SL(2, ZMod (p ^ n))))
    (m : ℕ) (hm : ∀ p : ℕ, p.Prime → p ∣ m → 5 ≤ p) :
    commutator (SL(2, ZMod m)) = ⊤ ∧ HasTrivialSchurMultiplier (SL(2, ZMod m)) := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | zero => exact absurd (hm 2 Nat.prime_two (dvd_zero 2)) (by norm_num)
  | one =>
    haveI : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
    haveI : Subsingleton (SL(2, ZMod 1)) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    exact ⟨Subsingleton.elim _ _, hasTrivialSchurMultiplier_of_subsingleton⟩
  | prime_pow p n hp' hn =>
    have h5 : 5 ≤ p := hm p hp' (dvd_pow_self p hn.ne')
    exact ⟨hP1 p n hp' h5 hn.ne', hP2 p n hp' h5 hn.ne'⟩
  | coprime a b ha hb hab iha ihb =>
    have ha' := iha fun p hp hpa => hm p hp (hpa.mul_right b)
    have hb' := ihb fun p hp hpb => hm p hp (hpb.mul_left a)
    set e := slZModMulEquiv hab
    refine ⟨commutator_eq_top_of_mulEquiv (commutator_prod_eq_top ha'.1 hb'.1) e, ?_⟩
    exact (hasTrivialSchurMultiplier_prod_of_perfect ha'.1 ha'.2 hb'.1 hb'.2).of_mulEquiv e

theorem five_le_of_prime_dvd_of_coprime {q m p : ℕ} (hq : q.Prime) (hmq : Nat.Coprime m q)
    (hm : Nat.Coprime m (q ^ 2 - 1)) (hp : p.Prime) (hpm : p ∣ m) : 5 ≤ p := by
  have hpq : ¬p ∣ q := fun h => by
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hpm hmq) h
    exact hp.one_lt.ne' this
  have hpq1 : ¬p ∣ q ^ 2 - 1 := fun h => by
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hpm hm) h
    exact hp.one_lt.ne' this

  have h6 : 2 ∣ q * (q ^ 2 - 1) ∧ 3 ∣ q * (q ^ 2 - 1) := by
    have hq1 : 1 ≤ q := hq.one_lt.le
    have hfac : q * (q ^ 2 - 1) = (q - 1) * q * (q + 1) := by
      zify [hq1, Nat.one_le_pow 2 q hq1]
      ring
    rw [hfac]
    constructor
    · rcases Nat.even_or_odd q with h | h
      · exact (h.two_dvd.mul_left _).mul_right _
      · have : Even (q + 1) := h.add_one
        exact this.two_dvd.mul_left _
    · have h3 : (q - 1) % 3 = 0 ∨ q % 3 = 0 ∨ (q + 1) % 3 = 0 := by omega
      rcases h3 with h | h | h
      · exact ((Nat.dvd_of_mod_eq_zero h).mul_right _).mul_right _
      · exact ((Nat.dvd_of_mod_eq_zero h).mul_left _).mul_right _
      · exact (Nat.dvd_of_mod_eq_zero h).mul_left _
  have hp2 : p ≠ 2 := by
    rintro rfl
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h6.1 with h | h
    · exact hpq h
    · exact hpq1 h
  have hp3 : p ≠ 3 := by
    rintro rfl
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h6.2 with h | h
    · exact hpq h
    · exact hpq1 h
  have h2 := hp.two_le
  have hp4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
  omega

end LargePrimes
p2m_reactivate "P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.Ihara"

end Inl_A3_SL2ZModFacts
p2m_reactivate "P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.Ihara"

section Inl_Thm_SL2_ZMod_schurTrivial_TransferEngine

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff MennickeCSP normalClosure_le_principalCongruenceAway qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ mem_mennickeZ_iff MennickeLemma21 mennickeLemma21_iff ZAway slToAway coe_slToAway zAwayToZMod zAwayToZMod_algebraMap mennickeQ_le_commutator_sup_mennickeQ_mul mennickeLemma21 normalClosure_mennickeA_eq_top"
p2m_open "Ihara"

theorem stemExtension_pow_index_eq_one' {E G : Type*} [Group E] [Group G]
    (π : E →* G) (hsurj : Function.Surjective π)
    (hcent : MonoidHom.ker π ≤ Subgroup.center E)
    (g : G) (hfin : (Subgroup.zpowers g).index ≠ 0)
    {x : E} (hx : x ∈ MonoidHom.ker π) (hxcomm : x ∈ commutator E) :
    x ^ (Subgroup.zpowers g).index = 1 := by
  classical
  have hidx : ((Subgroup.zpowers g).comap π).index = (Subgroup.zpowers g).index :=
    (Subgroup.zpowers g).index_comap_of_surjective hsurj
  haveI : ((Subgroup.zpowers g).comap π).FiniteIndex := ⟨by rw [hidx]; exact hfin⟩
  obtain ⟨c, hc⟩ := hsurj g

  have hsplit : ∀ u : E, u ∈ (Subgroup.zpowers g).comap π →
      ∃ (k : ℤ) (z : E), z ∈ MonoidHom.ker π ∧ u = c ^ k * z := by
    intro u hu
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp hu)
    refine ⟨k, (c ^ k)⁻¹ * u, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hc, hk, inv_mul_cancel]

  have hAcomm : ∀ u v : ↥((Subgroup.zpowers g).comap π), u * v = v * u := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    obtain ⟨k, z, hz, rfl⟩ := hsplit u hu
    obtain ⟨l, w, hw, rfl⟩ := hsplit v hv
    have hzc := Subgroup.mem_center_iff.mp (hcent hz)
    have hwc := Subgroup.mem_center_iff.mp (hcent hw)
    refine Subtype.ext ?_
    show c ^ k * z * (c ^ l * w) = c ^ l * w * (c ^ k * z)
    calc c ^ k * z * (c ^ l * w)
        = c ^ k * (z * c ^ l) * w := by group
      _ = c ^ k * (c ^ l * z) * w := by rw [← hzc (c ^ l)]
      _ = c ^ (k + l) * (z * w) := by rw [_root_.zpow_add]; group
      _ = c ^ (l + k) * (w * z) := by rw [add_comm k l, hwc z]
      _ = c ^ l * (c ^ k * w) * z := by rw [_root_.zpow_add]; group
      _ = c ^ l * (w * c ^ k) * z := by rw [hwc (c ^ k)]
      _ = c ^ l * w * (c ^ k * z) := by group
  letI : CommGroup ↥((Subgroup.zpowers g).comap π) :=
    { (inferInstance : Group ↥((Subgroup.zpowers g).comap π)) with mul_comm := hAcomm }

  have hkey : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * x ^ k * g₀ ∈ (Subgroup.zpowers g).comap π →
      g₀⁻¹ * x ^ k * g₀ = x ^ k := by
    intro k g₀ _
    have hxc : x ^ k ∈ Subgroup.center E := Subgroup.pow_mem _ (hcent hx) k
    rw [mul_assoc, ← Subgroup.mem_center_iff.mp hxc g₀, inv_mul_cancel_left]
  have htr := MonoidHom.transfer_eq_pow
    (MonoidHom.id ↥((Subgroup.zpowers g).comap π)) x hkey

  have hker1 :
      MonoidHom.transfer (MonoidHom.id ↥((Subgroup.zpowers g).comap π)) x = 1 :=
    MonoidHom.mem_ker.mp
      (Abelianization.commutator_subset_ker
        (MonoidHom.transfer (MonoidHom.id ↥((Subgroup.zpowers g).comap π)))
        hxcomm)
  rw [htr] at hker1
  have hval : x ^ ((Subgroup.zpowers g).comap π).index = 1 := by
    simpa using congrArg Subtype.val hker1
  rw [← hidx]
  exact hval

theorem stemExtension_pow_index_eq_one {E G : Type*} [Group E] [Group G]
    (π : E →* G) (hsurj : Function.Surjective π)
    (hcent : MonoidHom.ker π ≤ Subgroup.center E)
    (hcomm : MonoidHom.ker π ≤ commutator E)
    (g : G) (hfin : (Subgroup.zpowers g).index ≠ 0)
    {x : E} (hx : x ∈ MonoidHom.ker π) :
    x ^ (Subgroup.zpowers g).index = 1 :=
  stemExtension_pow_index_eq_one' π hsurj hcent g hfin hx (hcomm hx)

end Ihara
p2m_reactivate "P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.Ihara"

end Inl_Thm_SL2_ZMod_schurTrivial_TransferEngine
p2m_reactivate "P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.Ihara"

section Inl_A3_CompositeStep

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff MennickeCSP normalClosure_le_principalCongruenceAway qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ mem_mennickeZ_iff MennickeLemma21 mennickeLemma21_iff ZAway slToAway coe_slToAway zAwayToZMod zAwayToZMod_algebraMap mennickeQ_le_commutator_sup_mennickeQ_mul mennickeLemma21 normalClosure_mennickeA_eq_top"
p2m_open "Ihara"

open Subgroup Matrix

open scoped MatrixGroups

open scoped commutatorElement

universe u

section StemDescent

theorem ker_le_of_stem {G F : Type u} [Group G] [Group F] (red : G →* F) (hsurj : Function.Surjective red)
    (Q : Subgroup G) [Q.Normal] (hQker : Q ≤ red.ker) (hcen : ∀ g X : G, X ∈ red.ker → ⁅g, X⁆ ∈ Q)
    (hcomm : red.ker ≤ _root_.commutator G ⊔ Q) (hstem : HasTrivialSchurMultiplier F) :
    red.ker ≤ Q := by
  set f : G ⧸ Q →* F := QuotientGroup.lift Q red hQker with hfdef
  have hf_mk : ∀ g : G, f (QuotientGroup.mk g) = red g := fun g => rfl
  have hker_iff : ∀ g : G, (QuotientGroup.mk g : G ⧸ Q) ∈ f.ker ↔ g ∈ red.ker := by
    intro g
    rw [MonoidHom.mem_ker, hf_mk, MonoidHom.mem_ker]
  have hfsurj : Function.Surjective f := by
    intro Y
    obtain ⟨g, hg⟩ := hsurj Y
    exact ⟨QuotientGroup.mk g, by rw [hf_mk]; exact hg⟩
  have hfcen : f.ker ≤ Subgroup.center (G ⧸ Q) := by
    intro k hk
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q k
    rw [QuotientGroup.mk'_apply] at hk
    have hxN : x ∈ red.ker := (hker_iff x).mp hk
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q z
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq]
    have hcomm_elt : ⁅g⁻¹, x⁻¹⁆ ∈ Q := hcen g⁻¹ x⁻¹ (red.ker.inv_mem hxN)
    have hco : (g * x)⁻¹ * (x * g) = ⁅g⁻¹, x⁻¹⁆⁻¹ := by
      simp only [commutatorElement_def, _root_.mul_inv_rev, inv_inv]
      group
    rw [hco]
    exact Q.inv_mem hcomm_elt
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
    have hmaple : Subgroup.map (QuotientGroup.mk' Q) (_root_.commutator G) ≤ _root_.commutator (G ⧸ Q) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    have hcmem : QuotientGroup.mk' Q c ∈ Subgroup.map (QuotientGroup.mk' Q) (_root_.commutator G) :=
      Subgroup.mem_map_of_mem _ hc
    rw [QuotientGroup.mk'_apply] at hcmem
    exact hmaple hcmem
  have hker_bot : f.ker = ⊥ := hstem (G ⧸ Q) f hfsurj hfcen hfcomm
  intro x hx
  have hxker : (QuotientGroup.mk x : G ⧸ Q) ∈ f.ker := (hker_iff x).mpr hx
  rw [hker_bot, Subgroup.mem_bot] at hxker
  exact (QuotientGroup.eq_one_iff x).mp hxker

end StemDescent
p2m_reactivate "P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.Ihara"

section Bezout

variable (q : ℕ)

theorem mennickeQ_gcd_le_sup (a b : ℕ) : mennickeQ q (Nat.gcd a b) ≤ mennickeQ q a ⊔ mennickeQ q b := by
  apply Subgroup.normalClosure_le_normal
  rw [Set.singleton_subset_iff, SetLike.mem_coe]
  have heq : ((slToAway q mennickeA) ^ (Nat.gcd a b) : SL(2, ZAway q)) =
      ((slToAway q mennickeA) ^ a) ^ (Nat.gcdA a b) * ((slToAway q mennickeA) ^ b) ^ (Nat.gcdB a b) := by
    rw [← _root_.zpow_natCast, Nat.gcd_eq_gcd_ab, _root_.zpow_add, _root_.zpow_mul, _root_.zpow_mul, _root_.zpow_natCast, _root_.zpow_natCast]
  rw [heq]
  exact Subgroup.mul_mem _
    (Subgroup.zpow_mem _ (Subgroup.mem_sup_left (Subgroup.subset_normalClosure (Set.mem_singleton _))) _)
    (Subgroup.zpow_mem _ (Subgroup.mem_sup_right (Subgroup.subset_normalClosure (Set.mem_singleton _))) _)

variable [NeZero q]

theorem mennickeQ_sup_eq_top_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) : mennickeQ q a ⊔ mennickeQ q b = ⊤ := by
  rw [eq_top_iff]
  have h1 : mennickeQ q 1 = ⊤ := by
    show Subgroup.normalClosure ({(slToAway q mennickeA) ^ 1} : Set SL(2, ZAway q)) = ⊤
    exact normalClosure_mennickeA_pow_one_eq_top q
  rw [← h1, ← hab]
  exact mennickeQ_gcd_le_sup q a b

end Bezout
p2m_reactivate "P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.Ihara"

section Inf

variable (q : ℕ)

theorem mem_principalCongruenceAway_left_of_mul {m' m'' : ℕ} [NeZero m'] [NeZero m''] (hcop : Nat.Coprime m' m'')
    (hm'q : Nat.Coprime m' q) (hm''q : Nat.Coprime m'' q) (hmq : Nat.Coprime (m' * m'') q) {x : SL(2, ZAway q)}
    (hx : x ∈ principalCongruenceAway (m' * m'') q hmq) : x ∈ principalCongruenceAway m' q hm'q := by
  rw [principalCongruenceAway_mul_eq_inf q m' m'' hcop hm'q hm''q hmq, Subgroup.mem_inf] at hx
  exact hx.1

theorem mem_principalCongruenceAway_right_of_mul {m' m'' : ℕ} [NeZero m'] [NeZero m''] (hcop : Nat.Coprime m' m'')
    (hm'q : Nat.Coprime m' q) (hm''q : Nat.Coprime m'' q) (hmq : Nat.Coprime (m' * m'') q) {x : SL(2, ZAway q)}
    (hx : x ∈ principalCongruenceAway (m' * m'') q hmq) : x ∈ principalCongruenceAway m'' q hm''q := by
  rw [principalCongruenceAway_mul_eq_inf q m' m'' hcop hm'q hm''q hmq, Subgroup.mem_inf] at hx
  exact hx.2

theorem mennickeQ_mul_eq_inf [NeZero q] (m' m'' : ℕ) [NeZero m'] [NeZero m''] (hcop : Nat.Coprime m' m'')
    (hm'q : Nat.Coprime m' q) (hm''q : Nat.Coprime m'' q) (hmq : Nat.Coprime (m' * m'') q)
    (hm'n : Nat.Coprime m' (q ^ 2 - 1)) (hsat : (q ^ 2 - 1) ∣ m'') (hN' : MennickeCSP m' q hm'q)
    (hsurj' : Function.Surjective (slAwayReduction m' q hm'q))
    (hstem' : HasTrivialSchurMultiplier (SL(2, ZMod m'))) :
    mennickeQ q (m' * m'') = mennickeQ q m' ⊓ mennickeQ q m'' := by
  refine le_antisymm (le_inf (mennickeQ_le_of_dvd q m' (m' * m'') (dvd_mul_right m' m''))
    (mennickeQ_le_of_dvd q m'' (m' * m'') (dvd_mul_left m'' m'))) ?_
  have hN'eq : principalCongruenceAway m' q hm'q = mennickeQ q m' := hN'
  have hQm_le_N : mennickeQ q (m' * m'') ≤ principalCongruenceAway (m' * m'') q hmq :=
    normalClosure_le_principalCongruenceAway _ q hmq
  have hQ''_le_N'' : mennickeQ q m'' ≤ principalCongruenceAway m'' q hm''q :=
    normalClosure_le_principalCongruenceAway _ q hm''q
  have hQ''_le_Z : mennickeQ q m'' ≤ mennickeZ q (m' * m'') hmq := mennickeQ_le_mennickeZ_of_dvd q (m' * m'') m'' hmq hsat

  let red : mennickeQ q m'' →* SL(2, ZMod m') := (slAwayReduction m' q hm'q).comp (mennickeQ q m'').subtype
  have hred_ker : ∀ x : mennickeQ q m'', x ∈ red.ker ↔ (x : SL(2, ZAway q)) ∈ mennickeQ q m' := by
    intro x
    rw [MonoidHom.mem_ker, ← hN'eq, mem_principalCongruenceAway_iff]
    rfl

  have hsurj : Function.Surjective red := by
    intro Y
    obtain ⟨g, hg⟩ := hsurj' Y
    have hgmem : g ∈ ((mennickeQ q m' ⊔ mennickeQ q m'' : Subgroup SL(2, ZAway q)) : Set SL(2, ZAway q)) := by
      rw [mennickeQ_sup_eq_top_of_coprime q hcop]
      exact Subgroup.mem_top g
    rw [Subgroup.mul_normal (mennickeQ q m') (mennickeQ q m'')] at hgmem
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hgmem
    refine ⟨⟨b, hb⟩, ?_⟩
    have ha1 : slAwayReduction m' q hm'q a = 1 := by
      rw [← mem_principalCongruenceAway_iff, hN'eq]
      exact ha
    show slAwayReduction m' q hm'q b = Y
    rw [← hg, ← hab, map_mul, ha1, one_mul]

  let Q₀ : Subgroup (mennickeQ q m'') := (mennickeQ q (m' * m'')).subgroupOf (mennickeQ q m'')
  haveI hQ₀n : Q₀.Normal := Subgroup.Normal.subgroupOf inferInstance (mennickeQ q m'')
  have hQ₀ker : Q₀ ≤ red.ker := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [hred_ker, ← hN'eq]
    exact mem_principalCongruenceAway_left_of_mul q hcop hm'q hm''q hmq (hQm_le_N hx)

  have hcen : ∀ g X : mennickeQ q m'', X ∈ red.ker → ⁅g, X⁆ ∈ Q₀ := by
    intro g X hX
    rw [Subgroup.mem_subgroupOf]
    have hcoe : ((⁅g, X⁆ : mennickeQ q m'') : SL(2, ZAway q)) = ⁅(g : SL(2, ZAway q)), (X : SL(2, ZAway q))⁆ :=
      map_commutatorElement (mennickeQ q m'').subtype g X
    rw [hcoe]
    have hgZ : (g : SL(2, ZAway q)) ∈ mennickeZ q (m' * m'') hmq := hQ''_le_Z g.2
    have hXN' : (X : SL(2, ZAway q)) ∈ principalCongruenceAway m' q hm'q := by
      rw [hN'eq]
      exact (hred_ker X).mp hX
    have hXN : (X : SL(2, ZAway q)) ∈ principalCongruenceAway (m' * m'') q hmq := by
      rw [principalCongruenceAway_mul_eq_inf q m' m'' hcop hm'q hm''q hmq, Subgroup.mem_inf]
      exact ⟨hXN', hQ''_le_N'' X.2⟩
    exact (mem_mennickeZ_iff q (m' * m'') hmq g).mp hgZ _ hXN

  have hperf : ∀ x : mennickeQ q m'', x ∈ _root_.commutator (mennickeQ q m'') ⊔ Q₀ := by
    intro x
    have hx : (x : SL(2, ZAway q)) ∈
        ((⁅mennickeQ q m'', mennickeQ q m''⁆ ⊔ mennickeQ q (m' * m'') : Subgroup SL(2, ZAway q)) :
          Set SL(2, ZAway q)) :=
      mennickeQ_le_commutator_sup_mennickeQ_mul q m' m'' hcop hm'q hm''q hmq hm'n hsat x.2
    rw [Subgroup.mul_normal] at hx
    obtain ⟨c, hc, z, hz, hcz⟩ := Set.mem_mul.mp hx
    rw [SetLike.mem_coe, ← Subgroup.map_subtype_commutator, Subgroup.mem_map] at hc
    obtain ⟨c', hc', hcc'⟩ := hc
    have hzQ'' : z ∈ mennickeQ q m'' := by
      have hz' : z = c⁻¹ * x := by rw [← hcz, inv_mul_cancel_left]
      rw [hz', ← hcc']
      exact (mennickeQ q m'').mul_mem ((mennickeQ q m'').inv_mem c'.2) x.2
    have hxeq : x = c' * ⟨z, hzQ''⟩ := by
      apply Subtype.ext
      show (x : SL(2, ZAway q)) = (c' : SL(2, ZAway q)) * z
      rw [← hcz, ← hcc']
      rfl
    rw [hxeq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc')
      (Subgroup.mem_sup_right (by rw [Subgroup.mem_subgroupOf]; exact hz))
  have hcomm : red.ker ≤ _root_.commutator (mennickeQ q m'') ⊔ Q₀ := fun x _ => hperf x

  have hker : red.ker ≤ Q₀ := ker_le_of_stem red hsurj Q₀ hQ₀ker hcen hcomm hstem'
  intro x hx
  obtain ⟨hx', hx''⟩ := Subgroup.mem_inf.mp hx
  have hk : (⟨x, hx''⟩ : mennickeQ q m'') ∈ red.ker := (hred_ker ⟨x, hx''⟩).mpr hx'
  exact Subgroup.mem_subgroupOf.mp (hker hk)

end Inf
p2m_reactivate "P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.Ihara"

section Torsion

variable (q : ℕ)

theorem five_le_of_prime_dvd_block (m' : ℕ) {p : ℕ} (hp : p.Prime) (hpm : p ∣ m') (hm'q : Nat.Coprime m' q)
    (hm'n : Nat.Coprime m' (q ^ 2 - 1)) : 5 ≤ p := by
  have h3 := three_lt_of_prime_dvd_of_coprime q m' hp hpm hm'q hm'n
  exact hp.five_le_of_ne_two_of_ne_three (by omega) (by omega)

variable [NeZero q]

theorem pow_card_mem_mennickeQ_mul_impl (m' m₅ m₆ : ℕ) [NeZero m'] [NeZero m₅] [NeZero m₆]
    (hcop : Nat.Coprime m' (m₅ * m₆)) (h56 : Nat.Coprime m₅ m₆) (hm'q : Nat.Coprime m' q)
    (hm''q : Nat.Coprime (m₅ * m₆) q) (hmq : Nat.Coprime (m' * (m₅ * m₆)) q) (hm'n : Nat.Coprime m' (q ^ 2 - 1))
    (hsat : (q ^ 2 - 1) ∣ m₅ * m₆) (h5 : ∀ p : ℕ, p.Prime → p ∣ m₅ → 5 ≤ p)
    (hP1 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 → _root_.commutator (SL(2, ZMod (p ^ n))) = ⊤)
    (hP2 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 → HasTrivialSchurMultiplier (SL(2, ZMod (p ^ n))))
    (hN' : MennickeCSP m' q hm'q) (hsurj' : Function.Surjective (slAwayReduction m' q hm'q))
    (hZ'' : mennickeZ q (m₅ * m₆) hm''q = ⊤)
    (hhabel'' : principalCongruenceAway (m₅ * m₆) q hm''q ≤
      _root_.commutator (SL(2, ZAway q)) ⊔ mennickeQ q (m₅ * m₆))
    (hsurj'' : Function.Surjective (slAwayReduction (m₅ * m₆) q hm''q))
    {x : SL(2, ZAway q)} (hx : x ∈ principalCongruenceAway (m' * (m₅ * m₆)) q hmq) :
    x ^ Nat.card (SL(2, ZMod m₆)) ∈ mennickeQ q (m' * (m₅ * m₆)) := by
  haveI : NeZero (m₅ * m₆) := ⟨Nat.mul_ne_zero (NeZero.ne m₅) (NeZero.ne m₆)⟩

  have hstem' : HasTrivialSchurMultiplier (SL(2, ZMod m')) :=
    (commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod hP1 hP2 m'
      (fun p hp hpm => five_le_of_prime_dvd_block q m' hp hpm hm'q hm'n)).2
  rw [mennickeQ_mul_eq_inf q m' (m₅ * m₆) hcop hm'q hm''q hmq hm'n hsat hN' hsurj' hstem', Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  ·
    have hx' : x ∈ principalCongruenceAway m' q hm'q := mem_principalCongruenceAway_left_of_mul q hcop hm'q hm''q hmq hx
    have hN'eq : principalCongruenceAway m' q hm'q = mennickeQ q m' := hN'
    rw [hN'eq] at hx'
    exact Subgroup.pow_mem _ hx' _
  ·
    have hx'' : x ∈ principalCongruenceAway (m₅ * m₆) q hm''q :=
      mem_principalCongruenceAway_right_of_mul q hcop hm'q hm''q hmq hx
    have hQ''N : mennickeQ q (m₅ * m₆) ≤ (slAwayReduction (m₅ * m₆) q hm''q).ker :=
      normalClosure_le_principalCongruenceAway _ q hm''q
    let π₀ : SL(2, ZAway q) ⧸ mennickeQ q (m₅ * m₆) →* SL(2, ZMod (m₅ * m₆)) :=
      QuotientGroup.lift (mennickeQ q (m₅ * m₆)) (slAwayReduction (m₅ * m₆) q hm''q) hQ''N
    let π : SL(2, ZAway q) ⧸ mennickeQ q (m₅ * m₆) →* SL(2, ZMod m₅) × SL(2, ZMod m₆) :=
      (slZModMulEquiv h56).toMonoidHom.comp π₀
    have hπ_mk : ∀ g : SL(2, ZAway q), π (QuotientGroup.mk g) = slZModMulEquiv h56 (slAwayReduction (m₅ * m₆) q hm''q g) :=
      fun g => rfl
    have hπker : ∀ g : SL(2, ZAway q),
        (QuotientGroup.mk g : SL(2, ZAway q) ⧸ mennickeQ q (m₅ * m₆)) ∈ π.ker ↔
          g ∈ principalCongruenceAway (m₅ * m₆) q hm''q := by
      intro g
      rw [MonoidHom.mem_ker, hπ_mk, MulEquiv.map_eq_one_iff, mem_principalCongruenceAway_iff]
    have hπsurj : Function.Surjective π := by
      intro Y
      obtain ⟨g, hg⟩ := hsurj'' ((slZModMulEquiv h56).symm Y)
      exact ⟨QuotientGroup.mk g, by rw [hπ_mk, hg, MulEquiv.apply_symm_apply]⟩
    have hcent : π.ker ≤ Subgroup.center _ := by
      intro k hk
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective k
      have hgN := (hπker g).mp hk
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have hco : (h * g)⁻¹ * (g * h) = ⁅h⁻¹, g⁻¹⁆⁻¹ := by
        simp only [commutatorElement_def, _root_.mul_inv_rev, inv_inv]
        group
      rw [hco]
      refine Subgroup.inv_mem _ ?_
      have hhZ : h⁻¹ ∈ mennickeZ q (m₅ * m₆) hm''q := hZ'' ▸ Subgroup.mem_top _
      exact (mem_mennickeZ_iff q (m₅ * m₆) hm''q h⁻¹).mp hhZ g⁻¹ (Subgroup.inv_mem _ hgN)
    have hxker : (QuotientGroup.mk x : SL(2, ZAway q) ⧸ mennickeQ q (m₅ * m₆)) ∈ π.ker := (hπker x).mpr hx''
    have hxc : (QuotientGroup.mk x : SL(2, ZAway q) ⧸ mennickeQ q (m₅ * m₆)) ∈
        _root_.commutator (SL(2, ZAway q) ⧸ mennickeQ q (m₅ * m₆)) := by
      have hx_mem : x ∈ ((_root_.commutator (SL(2, ZAway q)) ⊔ mennickeQ q (m₅ * m₆) :
          Subgroup SL(2, ZAway q)) : Set SL(2, ZAway q)) := hhabel'' hx''
      rw [Subgroup.mul_normal] at hx_mem
      obtain ⟨c, hc, w, hw, hcw⟩ := Set.mem_mul.mp hx_mem
      have hmkw : (QuotientGroup.mk w : SL(2, ZAway q) ⧸ mennickeQ q (m₅ * m₆)) = 1 :=
        (QuotientGroup.eq_one_iff w).mpr hw
      have hmkx : (QuotientGroup.mk x : SL(2, ZAway q) ⧸ mennickeQ q (m₅ * m₆)) = QuotientGroup.mk c := by
        rw [← hcw, QuotientGroup.mk_mul, hmkw, mul_one]
      rw [hmkx]
      have hmaple : Subgroup.map (QuotientGroup.mk' (mennickeQ q (m₅ * m₆))) (_root_.commutator (SL(2, ZAway q))) ≤
          _root_.commutator (SL(2, ZAway q) ⧸ mennickeQ q (m₅ * m₆)) := by
        rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
        exact Subgroup.commutator_mono le_top le_top
      exact hmaple (Subgroup.mem_map_of_mem _ hc)

    obtain ⟨hperf₅, hstem₅⟩ := commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod hP1 hP2 m₅ h5
    have hF₆ : ∀ (E' : Type) [Group E'] (π' : E' →* SL(2, ZMod m₆)), Function.Surjective π' →
        π'.ker ≤ Subgroup.center E' → ∀ y ∈ π'.ker, y ∈ _root_.commutator E' →
          y ^ Nat.card (SL(2, ZMod m₆)) = 1 := by
      intro E' _ π' hs hc y hy hyc
      have hidx : (Subgroup.zpowers (1 : SL(2, ZMod m₆))).index = Nat.card (SL(2, ZMod m₆)) := by
        rw [Subgroup.zpowers_one_eq_bot, Subgroup.index_bot]
      have hfin : (Subgroup.zpowers (1 : SL(2, ZMod m₆))).index ≠ 0 := by
        rw [hidx]
        exact Nat.card_pos.ne'
      rw [← hidx]
      exact stemExtension_pow_index_eq_one' π' hs hc 1 hfin hy hyc
    have hpow := pow_eq_one_of_prod π hπsurj hcent hperf₅ hstem₅ hF₆ hxker hxc
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hpow
    exact hpow

end Torsion
p2m_reactivate "P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.Ihara"

end Inl_A3_CompositeStep
p2m_reactivate "P2MW.S_Ihara_pow_card_mem_mennickeQ_mul.Ihara"

open scoped MatrixGroups

theorem solution (q : ℕ) [NeZero q] (m' m₅ m₆ : ℕ) [NeZero m'] [NeZero m₅] [NeZero m₆]
    (hcop : Nat.Coprime m' (m₅ * m₆)) (h56 : Nat.Coprime m₅ m₆)
    (hm'q : Nat.Coprime m' q) (hm''q : Nat.Coprime (m₅ * m₆) q)
    (hmq : Nat.Coprime (m' * (m₅ * m₆)) q) (hm'n : Nat.Coprime m' (q ^ 2 - 1))
    (hsat : (q ^ 2 - 1) ∣ m₅ * m₆) (h5 : ∀ p : ℕ, p.Prime → p ∣ m₅ → 5 ≤ p)
    (hP1 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 → commutator (SL(2, ZMod (p ^ n))) = ⊤)
    (hP2 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 →
      Ihara.HasTrivialSchurMultiplier (SL(2, ZMod (p ^ n))))
    (hN' : Ihara.MennickeCSP m' q hm'q)
    (hsurj' : Function.Surjective (Ihara.slAwayReduction m' q hm'q))
    (hZ'' : Ihara.mennickeZ q (m₅ * m₆) hm''q = ⊤)
    (hhabel'' : Ihara.principalCongruenceAway (m₅ * m₆) q hm''q ≤
      commutator (SL(2, Ihara.ZAway q)) ⊔ Ihara.mennickeQ q (m₅ * m₆))
    (hsurj'' : Function.Surjective (Ihara.slAwayReduction (m₅ * m₆) q hm''q))
    {x : SL(2, Ihara.ZAway q)}
    (hx : x ∈ Ihara.principalCongruenceAway (m' * (m₅ * m₆)) q hmq) :
    x ^ Nat.card (SL(2, ZMod m₆)) ∈ Ihara.mennickeQ q (m' * (m₅ * m₆)) :=
  Ihara.pow_card_mem_mennickeQ_mul_impl q m' m₅ m₆ hcop h56 hm'q hm''q hmq hm'n hsat h5
    hP1 hP2 hN' hsurj' hZ'' hhabel'' hsurj'' hx

#print axioms solution

end S_Ihara_pow_card_mem_mennickeQ_mul
end P2MW
export P2MW.S_Ihara_pow_card_mem_mennickeQ_mul (solution)
