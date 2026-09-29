-- Prove2me | solution 1 for ModularCurve.FullLevel.two_mul_index_gammaH_levelH_sup_zpowers_neg_one_le_ncard_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/6d55afcc-9439-5d7e-ac1e-cb2acc91fe3f

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_CohCarrier_index_gammaH_eq_index_gamma0_mul_index
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_dedekindPsi_prime_pow
import Theorems.Thm_Matrix_SpecialLinearGroup_mem_sup_zpowers_neg_one_iff
import Theorems.Thm_CohCarrier_exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff
import Theorems.Thm_Matrix_SpecialLinearGroup_exists_map_eq_and_map_eq_of_coprime
import Theorems.Thm_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_sup_zpowers_neg_one_le_ncard_orbit
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

open scoped MatrixGroups Pointwise

noncomputable section

namespace P2M
namespace P3Count

open ModularCurve (dedekindPsi)

section LeftSide

theorem dedekindPsi_sq (n : ℕ) (hn : n ≠ 0) : dedekindPsi (n ^ 2) = n * dedekindPsi n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => exact absurd rfl hn
  | one => simp [ModularCurve.dedekindPsi_one]
  | prime_pow p k hp hk =>
    have hk0 : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
    rw [← pow_mul, ModularCurve.dedekindPsi_prime_pow p (k * 2) hp (by omega),
      ModularCurve.dedekindPsi_prime_pow p k hp hk0, mul_add, ← pow_add, ← pow_add]
    congr 2 <;> omega
  | coprime a b ha hb hab iha ihb =>
    rw [mul_pow, ModularCurve.dedekindPsi_mul_of_coprime _ _ (hab.pow 2 2),
      iha (by omega), ihb (by omega), ModularCurve.dedekindPsi_mul_of_coprime _ _ hab]
    ring

theorem dedekindPsi_sq_mul (N₀ M' : ℕ) (h0 : N₀ ≠ 0) (hcop : Nat.Coprime N₀ M') :
    dedekindPsi (N₀ ^ 2 * M') = N₀ * dedekindPsi N₀ * dedekindPsi M' := by
  rw [ModularCurve.dedekindPsi_mul_of_coprime _ _ (hcop.pow_left 2), dedekindPsi_sq N₀ h0]

theorem index_levelH (N₀ M' : ℕ) [NeZero (N₀ ^ 2 * M')] [NeZero N₀] :
    (ModularCurve.FullLevel.levelH N₀ M').index = Nat.totient N₀ := by
  unfold ModularCurve.FullLevel.levelH
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective _),
    Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

theorem neg_one_notMem_gammaH (N₀ M' : ℕ) (hN₀ : 3 ≤ N₀) [NeZero (N₀ ^ 2 * M')] :
    (-1 : SL(2, ℤ)) ∉ CohCarrier.GammaH (N₀ ^ 2 * M') (ModularCurve.FullLevel.levelH N₀ M') := by
  intro h
  obtain ⟨h0, hu⟩ := CohCarrier.mem_GammaH_iff.mp h
  rw [ModularCurve.FullLevel.mem_levelH_iff] at hu
  have hv := congrArg (fun u : (ZMod N₀)ˣ => (u : ZMod N₀)) hu
  simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units,
    Units.val_one] at hv
  have hG : (CongruenceSubgroup.Gamma0Map (N₀ ^ 2 * M') ⟨-1, h0⟩ : ZMod (N₀ ^ 2 * M')) = -1 := by
    show (((-1 : SL(2, ℤ)) 1 1 : ℤ) : ZMod (N₀ ^ 2 * M')) = -1
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq]
    push_cast
    rfl
  rw [hG, map_neg, map_one] at hv

  have h2 : ((2 : ℕ) : ZMod N₀) = 0 := by
    have : (1 : ZMod N₀) + 1 = 0 := by
      nth_rewrite 1 [← hv]
      rw [neg_add_cancel]
    rw [Nat.cast_two, ← this, one_add_one_eq_two]
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd two_pos h2
  omega

theorem two_mul_index_sup_zpowers_neg_one (Γ : Subgroup SL(2, ℤ)) (hΓ : (-1 : SL(2, ℤ)) ∉ Γ) :
    2 * (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index = Γ.index := by
  have hrel : Γ.relIndex (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨-1, Subgroup.mem_sup_right (Subgroup.mem_zpowers _), fun b hb => ?_⟩
    rw [Matrix.SpecialLinearGroup.mem_sup_zpowers_neg_one_iff] at hb
    rw [mul_neg_one]
    rcases hb with hb | hb
    · refine Or.inr ⟨hb, fun hnb => hΓ ?_⟩
      have := Γ.mul_mem hnb (Γ.inv_mem hb)
      rwa [neg_mul, mul_inv_cancel] at this
    · refine Or.inl ⟨hb, fun hb' => hΓ ?_⟩
      have := Γ.mul_mem hb (Γ.inv_mem hb')
      rwa [neg_mul, mul_inv_cancel] at this
  rw [← Subgroup.relIndex_mul_index (le_sup_left : Γ ≤ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))), hrel]

theorem lhs_eq (N₀ : ℕ) (hN₀ : 3 ≤ N₀) (M' : ℕ) [NeZero M'] (hcop : Nat.Coprime N₀ M') :
    2 * (CohCarrier.GammaH (N₀ ^ 2 * M') (ModularCurve.FullLevel.levelH N₀ M') ⊔
        Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      N₀ * Nat.totient N₀ * dedekindPsi N₀ * dedekindPsi M' := by
  haveI : NeZero N₀ := ⟨by omega⟩
  haveI : NeZero (N₀ ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero _ (NeZero.ne N₀)) (NeZero.ne M')⟩
  rw [two_mul_index_sup_zpowers_neg_one _ (neg_one_notMem_gammaH N₀ M' hN₀),
    CohCarrier.index_gammaH_eq_index_gamma0_mul_index, ModularCurve.Gamma0_index, index_levelH,
    dedekindPsi_sq_mul N₀ M' (NeZero.ne N₀) hcop]
  ring

end LeftSide

section GammaIndex

variable (n : ℕ) [NeZero n]

abbrev G1 : Subgroup SL(2, ℤ) := CohCarrier.GammaH n ⊥

theorem mem_G1_iff (γ : SL(2, ℤ)) :
    γ ∈ G1 n ↔ ((γ 1 0 : ℤ) : ZMod n) = 0 ∧ ((γ 1 1 : ℤ) : ZMod n) = 1 := by
  rw [CohCarrier.mem_GammaH_iff]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨CongruenceSubgroup.Gamma0_mem.mp h0, ?_⟩
    rw [Subgroup.mem_bot] at h1
    have := congrArg (fun u : (ZMod n)ˣ => (u : ZMod n)) h1
    simp only [CohCarrier.val_gamma0Units, Units.val_one] at this
    exact this
  · rintro ⟨hc, hd⟩
    refine ⟨CongruenceSubgroup.Gamma0_mem.mpr hc, ?_⟩
    rw [Subgroup.mem_bot]
    ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact hd

theorem ent00_of_mem_G1 {γ : SL(2, ℤ)} (h : γ ∈ G1 n) : ((γ 0 0 : ℤ) : ZMod n) = 1 := by
  obtain ⟨hc, hd⟩ := (mem_G1_iff n γ).mp h
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  have := congrArg (fun z : ℤ => (z : ZMod n)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, hd, mul_one, mul_zero, sub_zero] at this
  exact this

def beta : G1 n →* Multiplicative (ZMod n) where
  toFun γ := Multiplicative.ofAdd ((((γ : SL(2, ℤ)) 0 1 : ℤ) : ZMod n))
  map_one' := by simp
  map_mul' γ δ := by
    rw [← ofAdd_add]
    congr 1
    have h1 := ent00_of_mem_G1 n γ.2
    have h2 := ((mem_G1_iff n _).mp δ.2).2
    rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1, h2]
    ring

theorem beta_apply (γ : G1 n) :
    beta n γ = Multiplicative.ofAdd ((((γ : SL(2, ℤ)) 0 1 : ℤ) : ZMod n)) := rfl

theorem ker_beta : (beta n).ker = (CongruenceSubgroup.Gamma n).subgroupOf (G1 n) := by
  ext γ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, CongruenceSubgroup.Gamma_mem, beta_apply,
    ofAdd_eq_one]
  obtain ⟨hc, hd⟩ := (mem_G1_iff n _).mp γ.2
  have ha := ent00_of_mem_G1 n γ.2
  exact ⟨fun hb => ⟨ha, hb, hc, hd⟩, fun h => h.2.1⟩

theorem beta_surjective : Function.Surjective (beta n) := by
  intro t
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (Multiplicative.toAdd t)
  let A : SL(2, ℤ) := ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hA : A ∈ G1 n := (mem_G1_iff n A).mpr ⟨by simp [A], by simp [A]⟩
  refine ⟨⟨A, hA⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [beta_apply, toAdd_ofAdd, ← hk]
  simp [A]

theorem index_Gamma :
    (CongruenceSubgroup.Gamma n).index = n * Nat.totient n * dedekindPsi n := by
  have hle : CongruenceSubgroup.Gamma n ≤ G1 n := fun γ hγ => by
    rw [CongruenceSubgroup.Gamma_mem] at hγ
    exact (mem_G1_iff n γ).mpr ⟨hγ.2.2.1, hγ.2.2.2⟩
  have hrel : (CongruenceSubgroup.Gamma n).relIndex (G1 n) = n := by
    rw [Subgroup.relIndex, ← ker_beta, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr (beta_surjective n), Subgroup.card_top]
    exact Nat.card_zmod n
  have hG1 : (G1 n).index = dedekindPsi n * Nat.totient n := by
    rw [CohCarrier.index_gammaH_eq_index_gamma0_mul_index, ModularCurve.Gamma0_index,
      Subgroup.index_bot, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rw [← Subgroup.relIndex_mul_index hle, hrel, hG1]
  ring

end GammaIndex

section Scalars

variable {V : Type*} [AddCommGroup V] {n : ℕ} [NeZero n]

theorem nsmul_eq_mod_nsmul {E : V} (hE : n • E = 0) (k : ℕ) : k • E = (k % n) • E := by
  conv_lhs => rw [← Nat.mod_add_div k n, add_nsmul, mul_nsmul, hE, nsmul_zero, add_zero]

theorem val_natCast_nsmul {E : V} (hE : n • E = 0) (k : ℕ) : ((k : ZMod n).val) • E = k • E := by
  rw [ZMod.val_natCast, ← nsmul_eq_mod_nsmul hE]

theorem val_add_nsmul {E : V} (hE : n • E = 0) (u v : ZMod n) :
    (u + v).val • E = u.val • E + v.val • E := by
  rw [ZMod.val_add, ← nsmul_eq_mod_nsmul hE, add_nsmul]

theorem val_intCast_nsmul {E : V} (hE : n • E = 0) (k : ℤ) : ((k : ZMod n).val) • E = k • E := by
  rw [← natCast_zsmul, ZMod.val_intCast]
  conv_rhs => rw [← Int.emod_add_mul_ediv k n]
  rw [add_zsmul, mul_comm, mul_zsmul, natCast_zsmul, hE, zsmul_zero, add_zero]

theorem val_lin_nsmul {E : V} (hE : n • E = 0) (a b : ℤ) (x y : ZMod n) :
    ((a : ZMod n) * x + (b : ZMod n) * y).val • E = x.val • (a • E) + y.val • (b • E) := by
  have : (a : ZMod n) * x + (b : ZMod n) * y = ((a * x.val + b * y.val : ℤ) : ZMod n) := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [this, val_intCast_nsmul hE, add_zsmul, mul_comm a, mul_comm b, mul_zsmul, mul_zsmul,
    natCast_zsmul, natCast_zsmul]

end Scalars

section Action

variable (n : ℕ)

def ent (γ : SL(2, ℤ)) (i j : Fin 2) : ZMod n := ((γ i j : ℤ) : ZMod n)

abbrev red (γ : SL(2, ℤ)) : SL(2, ZMod n) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod n)) γ

theorem ent_eq_red (γ : SL(2, ℤ)) (i j : Fin 2) : ent n γ i j = red n γ i j := rfl

theorem ent_mul (g h : SL(2, ℤ)) (i j : Fin 2) :
    ent n (g * h) i j = ent n g i 0 * ent n h 0 j + ent n g i 1 * ent n h 1 j := by
  simp only [ent, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  ring

theorem ent_one (i j : Fin 2) : ent n 1 i j = if i = j then 1 else 0 := by
  simp only [ent, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
  split_ifs <;> simp

def act (γ : SL(2, ℤ)) (w : ZMod n × ZMod n) : ZMod n × ZMod n :=
  (ent n γ 0 0 * w.1 + ent n γ 0 1 * w.2, ent n γ 1 0 * w.1 + ent n γ 1 1 * w.2)

theorem act_one (w : ZMod n × ZMod n) : act n 1 w = w := by
  simp only [act, ent_one]
  simp

theorem act_mul (γ δ : SL(2, ℤ)) (w : ZMod n × ZMod n) :
    act n (γ * δ) w = act n γ (act n δ w) := by
  simp only [act, ent_mul]
  ext <;> ring

theorem act_add (γ : SL(2, ℤ)) (v w : ZMod n × ZMod n) :
    act n γ (v + w) = act n γ v + act n γ w := by
  simp only [act, Prod.fst_add, Prod.snd_add]
  ext <;> simp <;> ring

theorem act_smul (γ : SL(2, ℤ)) (s : ZMod n) (w : ZMod n × ZMod n) :
    act n γ (s • w) = s • act n γ w := by
  simp only [act, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ext <;> simp <;> ring

theorem act_congr {γ δ : SL(2, ℤ)} (h : red n γ = red n δ) (w : ZMod n × ZMod n) :
    act n γ w = act n δ w := by
  have : ∀ i j, ent n γ i j = ent n δ i j := fun i j => by rw [ent_eq_red, ent_eq_red, h]
  simp only [act, this]

theorem act_eq_self_of_mem_Gamma {γ : SL(2, ℤ)} (h : γ ∈ CongruenceSubgroup.Gamma n)
    (w : ZMod n × ZMod n) : act n γ w = w := by
  rw [CongruenceSubgroup.Gamma_mem] at h
  obtain ⟨h00, h01, h10, h11⟩ := h
  simp only [act, ent, h00, h01, h10, h11]
  simp

def rho : SL(2, ℤ) →* AddAut (ZMod n × ZMod n) where
  toFun γ :=
    { toFun := act n γ
      invFun := act n γ⁻¹
      left_inv := fun w => by rw [← act_mul, inv_mul_cancel, act_one]
      right_inv := fun w => by rw [← act_mul, mul_inv_cancel, act_one]
      map_add' := act_add n γ }
  map_one' := AddEquiv.ext fun w => act_one n w
  map_mul' γ δ := AddEquiv.ext fun w => act_mul n γ δ w

theorem rho_apply (γ : SL(2, ℤ)) (w : ZMod n × ZMod n) : rho n γ w = act n γ w := rfl

scoped instance instDistribMulAction (n : ℕ) : DistribMulAction SL(2, ℤ) (ZMod n × ZMod n) :=
  DistribMulAction.compHom _ (rho n)

theorem smul_def (γ : SL(2, ℤ)) (w : ZMod n × ZMod n) : γ • w = act n γ w := rfl

end Action

section Iota

variable {V : Type*} [AddCommGroup V] {n : ℕ} [NeZero n] {E₁ E₂ : V}

def iota (hE₁ : n • E₁ = 0) (hE₂ : n • E₂ = 0) : ZMod n × ZMod n →+ V where
  toFun w := w.1.val • E₁ + w.2.val • E₂
  map_zero' := by simp
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, val_add_nsmul hE₁, val_add_nsmul hE₂]
    abel

variable (hE₁ : n • E₁ = 0) (hE₂ : n • E₂ = 0)

theorem iota_apply (w : ZMod n × ZMod n) : iota hE₁ hE₂ w = w.1.val • E₁ + w.2.val • E₂ := rfl

theorem iota_intCast (a b : ℤ) :
    iota hE₁ hE₂ ((a : ZMod n), (b : ZMod n)) = a • E₁ + b • E₂ := by
  rw [iota_apply, val_intCast_nsmul hE₁, val_intCast_nsmul hE₂]

include hE₁ hE₂ in
theorem iota_injective (hind : ∀ a b : ℤ, a • E₁ + b • E₂ = 0 → (n : ℤ) ∣ a ∧ (n : ℤ) ∣ b) :
    Function.Injective (iota hE₁ hE₂) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨x, y⟩ h
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective y
  rw [iota_intCast] at h
  obtain ⟨ha, hb⟩ := hind a b h
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd a n).mpr ha, (ZMod.intCast_zmod_eq_zero_iff_dvd b n).mpr hb]
  rfl

include hE₁ hE₂ in
theorem exists_iota_eq (hspan : ∀ v : V, n • v = 0 → ∃ a b : ℤ, v = a • E₁ + b • E₂) {v : V}
    (hv : n • v = 0) : ∃ w, iota hE₁ hE₂ w = v := by
  obtain ⟨a, b, rfl⟩ := hspan v hv
  exact ⟨((a : ZMod n), (b : ZMod n)), iota_intCast hE₁ hE₂ a b⟩

theorem apply_iota (g : V →+ V) (γ : SL(2, ℤ))
    (h₁ : g E₁ = (γ 0 0 : ℤ) • E₁ + (γ 1 0 : ℤ) • E₂)
    (h₂ : g E₂ = (γ 0 1 : ℤ) • E₁ + (γ 1 1 : ℤ) • E₂) (w : ZMod n × ZMod n) :
    g (iota hE₁ hE₂ w) = iota hE₁ hE₂ (act n γ w) := by
  rw [iota_apply, iota_apply, map_add, map_nsmul, map_nsmul, h₁, h₂]
  simp only [act, ent]
  rw [val_lin_nsmul hE₁, val_lin_nsmul hE₂]
  simp only [smul_add]
  abel

end Iota

section Orbits

variable {n : ℕ} [NeZero n]

theorem mem_Gamma_of_act_eq (p₁ p₂ : ZMod n × ZMod n)
    (hind : ∀ a b : ℤ, a • p₁ + b • p₂ = 0 → (n : ℤ) ∣ a ∧ (n : ℤ) ∣ b)
    (γ : SL(2, ℤ)) (h₁ : act n γ p₁ = p₁) (h₂ : act n γ p₂ = p₂) :
    γ ∈ CongruenceSubgroup.Gamma n := by
  let L : ZMod n × ZMod n →+ ZMod n × ZMod n :=
    { toFun := fun st => st.1 • p₁ + st.2 • p₂
      map_zero' := by simp
      map_add' := fun u v => by
        simp only [Prod.fst_add, Prod.snd_add, add_smul]
        abel }
  have hL : ∀ st : ZMod n × ZMod n, L st = st.1 • p₁ + st.2 • p₂ := fun _ => rfl
  have hLinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨s, t⟩ hst
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective s
    obtain ⟨b, rfl⟩ := ZMod.intCast_surjective t
    rw [hL] at hst
    change (a : ZMod n) • p₁ + (b : ZMod n) • p₂ = 0 at hst
    rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul] at hst
    obtain ⟨ha, hb⟩ := hind a b hst
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd a n).mpr ha, (ZMod.intCast_zmod_eq_zero_iff_dvd b n).mpr hb]
    rfl
  have hLsurj : Function.Surjective L := Finite.surjective_of_injective hLinj
  have hlin : ∀ s t : ZMod n, act n γ (s • p₁ + t • p₂) = s • p₁ + t • p₂ := fun s t => by
    rw [act_add, act_smul, act_smul, h₁, h₂]
  obtain ⟨⟨s₁, t₁⟩, h10⟩ := hLsurj (1, 0)
  obtain ⟨⟨s₂, t₂⟩, h01⟩ := hLsurj (0, 1)
  rw [hL] at h10 h01
  have e1 := hlin s₁ t₁
  have e2 := hlin s₂ t₂
  simp only [h10] at e1
  simp only [h01] at e2
  simp only [act, mul_one, mul_zero, add_zero, zero_add, Prod.mk.injEq] at e1 e2
  rw [CongruenceSubgroup.Gamma_mem]
  exact ⟨e1.1, e2.1, e1.2, e2.2⟩

theorem stabilizer_pair (p₁ p₂ : ZMod n × ZMod n)
    (hind : ∀ a b : ℤ, a • p₁ + b • p₂ = 0 → (n : ℤ) ∣ a ∧ (n : ℤ) ∣ b) :
    MulAction.stabilizer SL(2, ℤ) ((p₁, p₂) : (ZMod n × ZMod n) × (ZMod n × ZMod n)) =
      CongruenceSubgroup.Gamma n := by
  ext γ
  rw [MulAction.mem_stabilizer_iff, Prod.smul_mk, Prod.mk.injEq, smul_def, smul_def]
  exact ⟨fun h => mem_Gamma_of_act_eq p₁ p₂ hind γ h.1 h.2,
    fun h => ⟨act_eq_self_of_mem_Gamma n h _, act_eq_self_of_mem_Gamma n h _⟩⟩

theorem ncard_orbit_pair (p₁ p₂ : ZMod n × ZMod n)
    (hind : ∀ a b : ℤ, a • p₁ + b • p₂ = 0 → (n : ℤ) ∣ a ∧ (n : ℤ) ∣ b) :
    (MulAction.orbit SL(2, ℤ) ((p₁, p₂) : (ZMod n × ZMod n) × (ZMod n × ZMod n))).ncard =
      n * Nat.totient n * dedekindPsi n := by
  rw [← MulAction.index_stabilizer, stabilizer_pair p₁ p₂ hind, index_Gamma]

variable {m : ℕ} [NeZero m]

theorem exists_act_eq_of_addOrderOf_eq (w : ZMod m × ZMod m) (hw : addOrderOf w = m) :
    ∃ γ : SL(2, ℤ), act m γ (0, 1) = w := by
  obtain ⟨hL1, -, -⟩ := CohCarrier.exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff m ⊤
  obtain ⟨a, ha1, ha2⟩ := hL1 w hw
  refine ⟨Matrix.SpecialLinearGroup.transpose a, ?_⟩
  simp only [act, ent, Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_apply, mul_zero,
    mul_one, zero_add]
  exact Prod.ext ha1 ha2

theorem isAddCyclic_and_card_iff (D : AddSubgroup (ZMod m × ZMod m)) :
    (IsAddCyclic D ∧ Nat.card D = m) ↔ ∃ w, addOrderOf w = m ∧ D = AddSubgroup.zmultiples w := by
  constructor
  · rintro ⟨hc, hcard⟩
    obtain ⟨w, rfl⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top D).mp hc
    exact ⟨w, by rw [← Nat.card_zmultiples, hcard], rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨inferInstance, by rw [Nat.card_zmultiples, hw]⟩

theorem smul_zmultiples (γ : SL(2, ℤ)) (w : ZMod m × ZMod m) :
    γ • AddSubgroup.zmultiples w = AddSubgroup.zmultiples (γ • w) := by
  ext v
  rw [AddSubgroup.mem_smul_pointwise_iff_exists, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hu
    refine ⟨k, ?_⟩
    show k • rho m γ w = rho m γ (k • w)
    rw [map_zsmul]
  · rintro ⟨k, rfl⟩
    refine ⟨k • w, AddSubgroup.mem_zmultiples_iff.mpr ⟨k, rfl⟩, ?_⟩
    show rho m γ (k • w) = k • rho m γ w
    rw [map_zsmul]

theorem orbit_eq_setOf_isAddCyclic (C₁ : AddSubgroup (ZMod m × ZMod m)) (hC : IsAddCyclic C₁)
    (hcard : Nat.card C₁ = m) :
    MulAction.orbit SL(2, ℤ) C₁ =
      {D : AddSubgroup (ZMod m × ZMod m) | IsAddCyclic D ∧ Nat.card D = m} := by
  obtain ⟨w, hw, rfl⟩ := (isAddCyclic_and_card_iff C₁).mp ⟨hC, hcard⟩
  obtain ⟨γw, hγw⟩ := exists_act_eq_of_addOrderOf_eq w hw
  ext D
  rw [MulAction.mem_orbit_iff, Set.mem_setOf_eq, isAddCyclic_and_card_iff]
  constructor
  · rintro ⟨γ, rfl⟩
    refine ⟨γ • w, ?_, smul_zmultiples γ w⟩
    rw [smul_def, ← rho_apply, AddEquiv.addOrderOf_eq, hw]
  · rintro ⟨w', hw', rfl⟩
    obtain ⟨γ', hγ'⟩ := exists_act_eq_of_addOrderOf_eq w' hw'
    refine ⟨γ' * γw⁻¹, ?_⟩
    rw [smul_zmultiples, smul_def, ← hγw, ← act_mul, inv_mul_cancel_right, hγ']

theorem ncard_orbit_cyclic (C₁ : AddSubgroup (ZMod m × ZMod m)) (hC : IsAddCyclic C₁)
    (hcard : Nat.card C₁ = m) : (MulAction.orbit SL(2, ℤ) C₁).ncard = dedekindPsi m := by
  rw [orbit_eq_setOf_isAddCyclic C₁ hC hcard, ← Nat.card_coe_set_eq,
    ← ZMod.natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi m]
  rfl

end Orbits

section Assembly

variable {V : Type*} [AddCommGroup V]

theorem basis_of_cofactor (n m : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) (B₁ B₂ : V)
    (hB₁ : (n * m) • B₁ = 0) (hB₂ : (n * m) • B₂ = 0)
    (hBi : ∀ a b : ℤ, a • B₁ + b • B₂ = 0 → ((n * m : ℕ) : ℤ) ∣ a ∧ ((n * m : ℕ) : ℤ) ∣ b)
    (hBs : ∀ v : V, (n * m) • v = 0 → ∃ a b : ℤ, v = a • B₁ + b • B₂) :
    n • (m • B₁) = 0 ∧ n • (m • B₂) = 0 ∧
    (∀ a b : ℤ, a • (m • B₁) + b • (m • B₂) = 0 → (n : ℤ) ∣ a ∧ (n : ℤ) ∣ b) ∧
    (∀ v : V, n • v = 0 → ∃ a b : ℤ, v = a • (m • B₁) + b • (m • B₂)) := by
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  refine ⟨by rw [smul_smul, hB₁], by rw [smul_smul, hB₂], fun a b hab => ?_, fun v hv => ?_⟩
  · rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul] at hab
    obtain ⟨ha, hb⟩ := hBi _ _ hab
    push_cast at ha hb
    exact ⟨(mul_dvd_mul_iff_right hm').mp ha, (mul_dvd_mul_iff_right hm').mp hb⟩
  · have hv' : (n * m) • v = 0 := by rw [mul_comm, ← smul_smul, hv, smul_zero]
    obtain ⟨a, b, rfl⟩ := hBs v hv'
    have h0 : ((n : ℤ) * a) • B₁ + ((n : ℤ) * b) • B₂ = 0 := by
      rw [← smul_smul, ← smul_smul, ← smul_add, natCast_zsmul, hv]
    obtain ⟨ha, hb⟩ := hBi _ _ h0
    push_cast at ha hb
    rw [mul_comm (n : ℤ) (m : ℤ)] at ha hb
    obtain ⟨a', rfl⟩ := (mul_dvd_mul_iff_right hn').mp
      ((mul_comm (n : ℤ) a) ▸ ha : (m : ℤ) * n ∣ a * n)
    obtain ⟨b', rfl⟩ := (mul_dvd_mul_iff_right hn').mp
      ((mul_comm (n : ℤ) b) ▸ hb : (m : ℤ) * n ∣ b * n)
    refine ⟨a', b', ?_⟩
    rw [← natCast_zsmul B₁ m, ← natCast_zsmul B₂ m, smul_smul, smul_smul, mul_comm a', mul_comm b']

theorem realise_nsmul (g : V →+ V) (m : ℕ) {B : V} (B₁ B₂ : V) (a c : ℤ)
    (h : g B = a • B₁ + c • B₂) : g (m • B) = a • (m • B₁) + c • (m • B₂) := by
  rw [map_nsmul, h, smul_add, smul_comm m a B₁, smul_comm m c B₂]

theorem main (N₀ : ℕ) (hN₀ : 3 ≤ N₀) (M' : ℕ) [NeZero M'] (hcop : Nat.Coprime N₀ M')
    (V : Type) [AddCommGroup V]
    (B₁ B₂ : V) (hB₁ : (N₀ * M') • B₁ = 0) (hB₂ : (N₀ * M') • B₂ = 0)
    (hBi : ∀ a b : ℤ, a • B₁ + b • B₂ = 0 → ((N₀ * M' : ℕ) : ℤ) ∣ a ∧ ((N₀ * M' : ℕ) : ℤ) ∣ b)
    (hBs : ∀ v : V, (N₀ * M') • v = 0 → ∃ a b : ℤ, v = a • B₁ + b • B₂)
    (P₁ P₂ : V) (hP₁ : N₀ • P₁ = 0) (hP₂ : N₀ • P₂ = 0)
    (hPi : ∀ a b : ℤ, a • P₁ + b • P₂ = 0 → (N₀ : ℤ) ∣ a ∧ (N₀ : ℤ) ∣ b)
    (C : AddSubgroup V) (hC : IsAddCyclic C) (hCM : Nat.card C = M')
    (G : Set (V ≃+ V))
    (hG : ∀ a b c d : ℤ, ((N₀ * M' : ℕ) : ℤ) ∣ a * d - b * c - 1 →
      ∃ g ∈ G, g B₁ = a • B₁ + c • B₂ ∧ g B₂ = b • B₁ + d • B₂) :
    N₀ * Nat.totient N₀ * dedekindPsi N₀ * dedekindPsi M' ≤
      {t : V × V × AddSubgroup V | ∃ g ∈ G, t = (g P₁, g P₂, C.map (g : V →+ V))}.ncard := by
  haveI : NeZero N₀ := ⟨by omega⟩
  have hM' : M' ≠ 0 := NeZero.ne M'

  obtain ⟨hE₁, hE₂, hEi, hEs⟩ := basis_of_cofactor N₀ M' (NeZero.ne N₀) hM' B₁ B₂ hB₁ hB₂ hBi hBs
  obtain ⟨hF₁, hF₂, hFi, hFs⟩ := basis_of_cofactor M' N₀ hM' (NeZero.ne N₀) B₁ B₂
    (by rwa [mul_comm]) (by rwa [mul_comm]) (by rwa [mul_comm]) (by rwa [mul_comm])
  set ι₀ : ZMod N₀ × ZMod N₀ →+ V := iota hE₁ hE₂ with hι₀_def
  set ι₁ : ZMod M' × ZMod M' →+ V := iota hF₁ hF₂ with hι₁_def
  have hι₀ : Function.Injective ι₀ := iota_injective hE₁ hE₂ hEi
  have hι₁ : Function.Injective ι₁ := iota_injective hF₁ hF₂ hFi

  obtain ⟨p₁, hp₁⟩ := exists_iota_eq hE₁ hE₂ hEs hP₁
  obtain ⟨p₂, hp₂⟩ := exists_iota_eq hE₁ hE₂ hEs hP₂
  have hpi : ∀ a b : ℤ, a • p₁ + b • p₂ = 0 → (N₀ : ℤ) ∣ a ∧ (N₀ : ℤ) ∣ b := fun a b h =>
    hPi a b (by
      have := congrArg ι₀ h
      rw [map_add, map_zsmul, map_zsmul, map_zero] at this
      rw [← hp₁, ← hp₂]
      exact this)

  have hCtor : ∀ c ∈ C, M' • c = 0 := fun c hc => by
    have := card_nsmul_eq_zero' (G := C) (x := ⟨c, hc⟩)
    rw [hCM] at this
    exact congrArg Subtype.val this
  have hCle : C ≤ ι₁.range := fun c hc => exists_iota_eq hF₁ hF₂ hFs (hCtor c hc)
  set C₁ : AddSubgroup (ZMod M' × ZMod M') := C.comap ι₁ with hC₁_def
  have hC₁ : C₁.map ι₁ = C := AddSubgroup.map_comap_eq_self hCle
  have eC : C₁ ≃+ C := (C₁.equivMapOfInjective ι₁ hι₁).trans (AddEquiv.addSubgroupCongr hC₁)
  have hC₁cyc : IsAddCyclic C₁ := isAddCyclic_of_surjective eC.symm eC.symm.surjective
  have hC₁card : Nat.card C₁ = M' := by rw [Nat.card_congr eC.toEquiv, hCM]

  set x₀ : (ZMod N₀ × ZMod N₀) × (ZMod N₀ × ZMod N₀) := (p₁, p₂) with hx₀_def
  have hOp : (MulAction.orbit SL(2, ℤ) x₀).ncard = N₀ * Nat.totient N₀ * dedekindPsi N₀ :=
    ncard_orbit_pair p₁ p₂ hpi
  have hOc : (MulAction.orbit SL(2, ℤ) C₁).ncard = dedekindPsi M' :=
    ncard_orbit_cyclic C₁ hC₁cyc hC₁card

  let F : ((ZMod N₀ × ZMod N₀) × (ZMod N₀ × ZMod N₀)) × AddSubgroup (ZMod M' × ZMod M') →
      V × V × AddSubgroup V := fun z => (ι₀ z.1.1, ι₀ z.1.2, z.2.map ι₁)
  have hF : ∀ z, F z = (ι₀ z.1.1, ι₀ z.1.2, z.2.map ι₁) := fun _ => rfl
  have hFinj : Function.Injective F := by
    rintro ⟨⟨q₁, q₂⟩, D⟩ ⟨⟨q₁', q₂'⟩, D'⟩ h
    simp only [hF, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [hι₀ h1, hι₀ h2, AddSubgroup.map_injective hι₁ h3]

  have hFS : F '' (MulAction.orbit SL(2, ℤ) x₀ ×ˢ MulAction.orbit SL(2, ℤ) C₁) ⊆
      {t : V × V × AddSubgroup V | ∃ g ∈ G, t = (g P₁, g P₂, C.map (g : V →+ V))} := by
    rintro _ ⟨⟨q, D⟩, ⟨hq, hD⟩, rfl⟩
    obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.mp hq
    obtain ⟨δ, rfl⟩ := MulAction.mem_orbit_iff.mp hD
    obtain ⟨ε, hεγ, hεδ⟩ := Matrix.SpecialLinearGroup.exists_map_eq_and_map_eq_of_coprime N₀ M'
      hcop (red N₀ γ) (red M' δ)
    have hdet : ((N₀ * M' : ℕ) : ℤ) ∣ (ε 0 0 : ℤ) * ε 1 1 - ε 0 1 * ε 1 0 - 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe ε
      rw [Matrix.det_fin_two] at h
      rw [h, sub_self]
      exact dvd_zero _
    obtain ⟨g, hg, hg₁, hg₂⟩ := hG (ε 0 0) (ε 0 1) (ε 1 0) (ε 1 1) hdet
    refine ⟨g, hg, ?_⟩
    have hg0 : ∀ w, g (ι₀ w) = ι₀ (act N₀ ε w) := fun w =>
      apply_iota hE₁ hE₂ (g : V →+ V) ε (realise_nsmul (g : V →+ V) M' B₁ B₂ _ _ hg₁)
        (realise_nsmul (g : V →+ V) M' B₁ B₂ _ _ hg₂) w
    have hg1 : ∀ w, g (ι₁ w) = ι₁ (act M' ε w) := fun w =>
      apply_iota hF₁ hF₂ (g : V →+ V) ε (realise_nsmul (g : V →+ V) N₀ B₁ B₂ _ _ hg₁)
        (realise_nsmul (g : V →+ V) N₀ B₁ B₂ _ _ hg₂) w
    rw [hF]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show ι₀ (γ • x₀).1 = g P₁
      rw [hx₀_def, Prod.smul_fst, smul_def, ← act_congr N₀ hεγ, ← hg0, hp₁]
    · show ι₀ (γ • x₀).2 = g P₂
      rw [hx₀_def, Prod.smul_snd, smul_def, ← act_congr N₀ hεγ, ← hg0, hp₂]
    · show (δ • C₁).map ι₁ = C.map (g : V →+ V)
      ext v
      simp only [AddSubgroup.mem_map]
      constructor
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨c, hc, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists u δ C₁).mp hu
        refine ⟨ι₁ c, ?_, ?_⟩
        · rw [← hC₁]
          exact AddSubgroup.mem_map_of_mem _ hc
        · rw [AddMonoidHom.coe_coe, hg1, smul_def, act_congr M' hεδ]
      · rintro ⟨v', hv', rfl⟩
        rw [← hC₁] at hv'
        obtain ⟨c, hc, rfl⟩ := AddSubgroup.mem_map.mp hv'
        refine ⟨δ • c, (AddSubgroup.mem_smul_pointwise_iff_exists _ δ C₁).mpr ⟨c, hc, rfl⟩, ?_⟩
        rw [AddMonoidHom.coe_coe, hg1, smul_def, act_congr M' hεδ]

  haveI : Finite (AddSubgroup (ZMod M' × ZMod M')) :=
    Finite.of_injective (fun D : AddSubgroup (ZMod M' × ZMod M') => (D : Set (ZMod M' × ZMod M')))
      SetLike.coe_injective
  have hSfin : {t : V × V × AddSubgroup V | ∃ g ∈ G, t = (g P₁, g P₂, C.map (g : V →+ V))}.Finite := by
    refine (Set.finite_range F).subset ?_
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨q₁, hq₁⟩ := exists_iota_eq hE₁ hE₂ hEs (v := g P₁) (by rw [← map_nsmul, hP₁, map_zero])
    obtain ⟨q₂, hq₂⟩ := exists_iota_eq hE₁ hE₂ hEs (v := g P₂) (by rw [← map_nsmul, hP₂, map_zero])
    refine ⟨((q₁, q₂), (C.map (g : V →+ V)).comap ι₁), ?_⟩
    rw [hF]
    refine Prod.ext hq₁ (Prod.ext hq₂ ?_)
    show ((C.map (g : V →+ V)).comap ι₁).map ι₁ = C.map (g : V →+ V)
    refine AddSubgroup.map_comap_eq_self ?_
    rintro _ ⟨c, hc, rfl⟩
    exact exists_iota_eq hF₁ hF₂ hFs
      (by rw [AddMonoidHom.coe_coe, ← map_nsmul, hCtor c hc, map_zero])

  calc N₀ * Nat.totient N₀ * dedekindPsi N₀ * dedekindPsi M'
      = (MulAction.orbit SL(2, ℤ) x₀ ×ˢ MulAction.orbit SL(2, ℤ) C₁).ncard := by
        rw [Set.ncard_prod, hOp, hOc]
    _ = (F '' (MulAction.orbit SL(2, ℤ) x₀ ×ˢ MulAction.orbit SL(2, ℤ) C₁)).ncard :=
        (Set.ncard_image_of_injective _ hFinj).symm
    _ ≤ _ := Set.ncard_le_ncard hFS hSfin

end Assembly

end P2M.P3Count

end

open P2M.P3Count in

theorem solution
    (N₀ : ℕ) (hN₀ : 3 ≤ N₀) (M' : ℕ) [NeZero M'] (hcop : Nat.Coprime N₀ M')
    (V : Type) [AddCommGroup V]
    (B₁ B₂ : V) (hB₁ : (N₀ * M') • B₁ = 0) (hB₂ : (N₀ * M') • B₂ = 0)
    (hBi : ∀ a b : ℤ, a • B₁ + b • B₂ = 0 → ((N₀ * M' : ℕ) : ℤ) ∣ a ∧ ((N₀ * M' : ℕ) : ℤ) ∣ b)
    (hBs : ∀ v : V, (N₀ * M') • v = 0 → ∃ a b : ℤ, v = a • B₁ + b • B₂)
    (P₁ P₂ : V) (hP₁ : N₀ • P₁ = 0) (hP₂ : N₀ • P₂ = 0)
    (hPi : ∀ a b : ℤ, a • P₁ + b • P₂ = 0 → (N₀ : ℤ) ∣ a ∧ (N₀ : ℤ) ∣ b)
    (C : AddSubgroup V) (hC : IsAddCyclic C) (hCM : Nat.card C = M')
    (G : Set (V ≃+ V))
    (hG : ∀ a b c d : ℤ, ((N₀ * M' : ℕ) : ℤ) ∣ a * d - b * c - 1 →
      ∃ g ∈ G, g B₁ = a • B₁ + c • B₂ ∧ g B₂ = b • B₁ + d • B₂) :
    2 * (CohCarrier.GammaH (N₀ ^ 2 * M') (ModularCurve.FullLevel.levelH N₀ M') ⊔
        Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
      {t : V × V × AddSubgroup V | ∃ g ∈ G, t = (g P₁, g P₂, C.map (g : V →+ V))}.ncard := by
  rw [lhs_eq N₀ hN₀ M' hcop]
  exact main N₀ hN₀ M' hcop V B₁ B₂ hB₁ hB₂ hBi hBs P₁ P₂ hP₁ hP₂ hPi C hC hCM G hG

end S_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_sup_zpowers_neg_one_le_ncard_orbit
end P2MW
export P2MW.S_ModularCurve_FullLevel_two_mul_index_gammaH_levelH_sup_zpowers_neg_one_le_ncard_orbit (solution)
