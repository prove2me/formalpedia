-- Prove2me | solution 1 for ModularForm.eta_pow_twentyfour_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/45e76e17-9d61-517c-a415-339c74eb6946

import Mathlib
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_hasSum_coeff_etaProd_pow
import Theorems.Thm_ModularCurve_hasSum_qParam_mul
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_dedekindPsi_prime_pow
import Theorems.Thm_CuspForm_exists_gamma0_four_apply_eq_eta_pow_mul
import Theorems.Thm_ModularForm_sturm_bound_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_eta_pow_twentyfour_eq
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option maxHeartbeats 6400000
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularForm_eta_pow_twentyfour_eq.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "etaProd hasSum_coeff_etaProd_pow hasSum_qParam_mul Gamma0_index dedekindPsi_prime_pow"
p2m_open "ModularCurve"
namespace ARails

open Complex
open scoped MatrixGroups
local notation "𝕢" => Function.Periodic.qParam

theorem T_mem_Gamma0 (N : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
  rw [CongruenceSubgroup.Gamma0_mem, ModularGroup.coe_T]
  simp

theorem one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma0 N)]
  exact AddSubgroup.mem_zmultiples 1

theorem index_Gamma0_four : (CongruenceSubgroup.Gamma0 4).index = 6 := by
  rw [ModularCurve.Gamma0_index, show (4 : ℕ) = 2 ^ 2 by norm_num,
    ModularCurve.dedekindPsi_prime_pow 2 2 Nat.prime_two two_ne_zero]
  norm_num

def toMF {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [ModularFormClass F Γ k] (f : F) : ModularForm Γ k where
  toFun := f
  slash_action_eq' := SlashInvariantFormClass.slash_action_eq f
  holo' := ModularFormClass.holo f
  bdd_at_cusps' := ModularFormClass.bdd_at_cusps f

@[scoped simp] theorem toMF_apply {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [ModularFormClass F Γ k] (f : F) (z : UpperHalfPlane) : toMF f z = f z := rfl

theorem qParam_two_mul (z : ℂ) : 𝕢 1 (2 * z) = 𝕢 1 z ^ 2 := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, ← exp_nat_mul]; congr 1; push_cast; ring
theorem qParam_four_mul (z : ℂ) : 𝕢 1 (4 * z) = 𝕢 1 z ^ 4 := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, ← exp_nat_mul]; congr 1; push_cast; ring

theorem qParam24_prefactor (z : ℂ) (a b c e : ℕ) (he : a + 2 * b + 4 * c = 24 * e) :
    𝕢 24 z ^ a * 𝕢 24 (2 * z) ^ b * 𝕢 24 (4 * z) ^ c = 𝕢 1 z ^ e := by
  simp only [Function.Periodic.qParam, ← exp_nat_mul, ← exp_add]
  congr 1
  have h : (a : ℂ) + 2 * b + 4 * c = 24 * e := by exact_mod_cast he
  push_cast
  linear_combination (2 * Real.pi * I * z / 24) * h

def QS (A : PowerSeries ℂ) (F : UpperHalfPlane → ℂ) : Prop :=
  ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => PowerSeries.coeff m A * 𝕢 1 (τ : ℂ) ^ m) (F τ)

theorem QS.mul {A B : PowerSeries ℂ} {F G : UpperHalfPlane → ℂ} (hA : QS A F) (hB : QS B G) :
    QS (A * B) (fun τ => F τ * G τ) := fun τ =>
  ModularCurve.hasSum_qParam_mul 1 one_pos A B F G hA hB τ

theorem QS_X_pow (e : ℕ) : QS (PowerSeries.X ^ e) (fun τ => 𝕢 1 (τ : ℂ) ^ e) := fun τ => by
  have := hasSum_single (f := fun m : ℕ => PowerSeries.coeff m ((PowerSeries.X : PowerSeries ℂ) ^ e) *
    𝕢 1 (τ : ℂ) ^ m) e (fun m hm => by simp [PowerSeries.coeff_X_pow, hm])
  simpa [PowerSeries.coeff_X_pow] using this

theorem hasSum_coeff_expand (k : ℕ) (hk : k ≠ 0) (G : PowerSeries ℤ) {q g : ℂ}
    (h : HasSum (fun m : ℕ => ((PowerSeries.coeff m G : ℤ) : ℂ) * (q ^ k) ^ m) g) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (PowerSeries.expand k hk (G.map (Int.castRingHom ℂ))) * q ^ n) g := by
  let i : ℕ → ℕ := fun m => k * m
  have hi : Function.Injective i := fun a b hab => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) hab
  have hoff : ∀ n ∉ Set.range i,
      PowerSeries.coeff n (PowerSeries.expand k hk (G.map (Int.castRingHom ℂ))) * q ^ n = 0 := by
    intro n hn
    rw [PowerSeries.coeff_expand, if_neg, zero_mul]
    rintro ⟨m, rfl⟩
    exact hn ⟨m, rfl⟩
  refine (hi.hasSum_iff hoff).mp ?_
  convert h using 1
  funext m
  simp only [Function.comp_apply, i]
  rw [PowerSeries.coeff_expand, if_pos (dvd_mul_right k m), Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hk),
    PowerSeries.coeff_map, pow_mul]
  rfl

theorem QS_etaProd_pow (a : ℕ) :
    QS ((etaProd ^ a).map (Int.castRingHom ℂ)) (fun τ => (∏' n : ℕ, (1 - 𝕢 1 (τ : ℂ) ^ (n + 1))) ^ a) :=
  fun τ => by
  have h := ModularCurve.hasSum_coeff_etaProd_pow a (q := 𝕢 1 (τ : ℂ)) (by simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ)
  convert h using 2 with m <;> simp [← map_pow, PowerSeries.coeff_map]

theorem QS_expand_etaProd_pow (k : ℕ) (hk : k ≠ 0) (a : ℕ) :
    QS (PowerSeries.expand k hk ((etaProd ^ a).map (Int.castRingHom ℂ)))
      (fun τ => (∏' n : ℕ, (1 - (𝕢 1 (τ : ℂ) ^ k) ^ (n + 1))) ^ a) := fun τ => by
  have hq : ‖𝕢 1 (τ : ℂ) ^ k‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (by simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ) hk
  exact hasSum_coeff_expand k hk (etaProd ^ a) (ModularCurve.hasSum_coeff_etaProd_pow a hq)

private noncomputable def _root_.ModularCurve.ARails.S (a b c e : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ e * (etaProd ^ a * PowerSeries.expand 2 two_ne_zero (etaProd ^ b) *
    PowerSeries.expand 4 (by norm_num) (etaProd ^ c))

p2m_export "ModularCurve.ARails" "S"
theorem S_map (a b c e : ℕ) : (S a b c e).map (Int.castRingHom ℂ) =
    PowerSeries.X ^ e * ((etaProd ^ a).map (Int.castRingHom ℂ) *
      PowerSeries.expand 2 two_ne_zero ((etaProd ^ b).map (Int.castRingHom ℂ)) *
      PowerSeries.expand 4 (by norm_num) ((etaProd ^ c).map (Int.castRingHom ℂ))) := by
  simp only [S, map_mul, map_pow, PowerSeries.map_X, PowerSeries.map_expand]

theorem eta_eq (z : ℂ) : ModularForm.eta z = 𝕢 24 z * ∏' n : ℕ, (1 - 𝕢 1 z ^ (n + 1)) := rfl

theorem hasSum_etaProduct (a b c e : ℕ) (he : a + 2 * b + 4 * c = 24 * e) (z : UpperHalfPlane) :
    HasSum (fun m : ℕ => ((PowerSeries.coeff m (S a b c e) : ℤ) : ℂ) * 𝕢 1 (z : ℂ) ^ m)
      (ModularForm.eta (z : ℂ) ^ a * ModularForm.eta (2 * (z : ℂ)) ^ b * ModularForm.eta (4 * (z : ℂ)) ^ c) := by
  have hQ := ((QS_X_pow e).mul (((QS_etaProd_pow a).mul (QS_expand_etaProd_pow 2 two_ne_zero b)).mul
    (QS_expand_etaProd_pow 4 (by norm_num) c))) z
  rw [← S_map] at hQ
  simp only [PowerSeries.coeff_map, eq_intCast] at hQ
  convert hQ using 1
  simp only [eta_eq, mul_pow, qParam_two_mul, qParam_four_mul]
  rw [← qParam24_prefactor (z : ℂ) a b c e he]
  ring

theorem qExpansion_coeff_eq {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 4) k) (a b c e : ℕ)
    (he : a + 2 * b + 4 * c = 24 * e)
    (hf : ∀ z : UpperHalfPlane, f z = ModularForm.eta (z : ℂ) ^ a * ModularForm.eta (2 * (z : ℂ)) ^ b *
      ModularForm.eta (4 * (z : ℂ)) ^ c) (m : ℕ) :
    (UpperHalfPlane.qExpansion 1 f).coeff m = ((PowerSeries.coeff m (S a b c e) : ℤ) : ℂ) := by
  symm
  refine ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods_Gamma0 4) (f := f)
    (c := fun m => ((PowerSeries.coeff m (S a b c e) : ℤ) : ℂ)) (fun τ => ?_) m
  simpa only [smul_eq_mul, hf] using hasSum_etaProduct a b c e he τ

def Rep (N : ℕ) (L : List ℤ) (F : PowerSeries ℤ) : Prop := ∀ m, m < N → L.getD m 0 = PowerSeries.coeff m F

def oneL (N : ℕ) : List ℤ := (List.range N).map fun m => if m = 0 then 1 else 0
def XpowL (N e : ℕ) : List ℤ := (List.range N).map fun m => if m = e then 1 else 0

def facL (N k : ℕ) : List ℤ := (List.range N).map fun m => (if m = 0 then 1 else 0) - (if m = k then 1 else 0)
def mulL (N : ℕ) (u v : List ℤ) : List ℤ :=
  (List.range N).map fun m => ∑ i ∈ Finset.range (m + 1), u.getD i 0 * v.getD (m - i) 0
def powL (N : ℕ) (u : List ℤ) : ℕ → List ℤ
  | 0 => oneL N
  | n + 1 => mulL N (powL N u n) u
def expandL (N k : ℕ) (u : List ℤ) : List ℤ :=
  (List.range N).map fun m => if k ∣ m then u.getD (m / k) 0 else 0

def etaL (N : ℕ) : List ℤ := ((List.range N).map fun n => facL N (n + 1)).foldr (mulL N) (oneL N)

theorem getD_map_range {N m : ℕ} (hm : m < N) (g : ℕ → ℤ) : ((List.range N).map g).getD m 0 = g m := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm]
  rfl

theorem Rep.one (N : ℕ) : Rep N (oneL N) 1 := fun m hm => by
  rw [oneL, getD_map_range hm, PowerSeries.coeff_one]

theorem Rep.Xpow (N e : ℕ) : Rep N (XpowL N e) (PowerSeries.X ^ e) := fun m hm => by
  rw [XpowL, getD_map_range hm, PowerSeries.coeff_X_pow]

theorem Rep.fac (N k : ℕ) : Rep N (facL N k) (1 - PowerSeries.X ^ k) := fun m hm => by
  rw [facL, getD_map_range hm, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]

theorem Rep.mul {N : ℕ} {u v : List ℤ} {F G : PowerSeries ℤ} (hu : Rep N u F) (hv : Rep N v G) :
    Rep N (mulL N u v) (F * G) := fun m hm => by
  rw [mulL, getD_map_range hm, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  rw [hu i (by omega), hv (m - i) (by omega)]

theorem Rep.pow {N : ℕ} {u : List ℤ} {F : PowerSeries ℤ} (hu : Rep N u F) (n : ℕ) : Rep N (powL N u n) (F ^ n) := by
  induction n with
  | zero => simpa [powL] using Rep.one N
  | succ n ih => rw [powL, pow_succ]; exact ih.mul hu

theorem Rep.expand {N k : ℕ} (hk : k ≠ 0) {u : List ℤ} {F : PowerSeries ℤ} (hu : Rep N u F) :
    Rep N (expandL N k u) (PowerSeries.expand k hk F) := fun m hm => by
  rw [expandL, getD_map_range hm, PowerSeries.coeff_expand]
  split_ifs with h
  · exact hu _ (lt_of_le_of_lt (Nat.div_le_self m k) hm)
  · rfl

theorem Rep.foldr {N : ℕ} (l : List (List ℤ × PowerSeries ℤ)) (hl : ∀ p ∈ l, Rep N p.1 p.2) :
    Rep N ((l.map Prod.fst).foldr (mulL N) (oneL N)) ((l.map Prod.snd).prod) := by
  induction l with
  | nil => simpa using Rep.one N
  | cons p l ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons]
    exact (hl p (List.mem_cons_self)).mul (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))

def Cong (m : ℕ) (G : PowerSeries ℤ) : Prop := (PowerSeries.X : PowerSeries ℤ) ^ (m + 1) ∣ G - 1

theorem Cong.mul {m : ℕ} {G H : PowerSeries ℤ} (hG : Cong m G) (hH : Cong m H) : Cong m (G * H) := by
  have : G * H - 1 = (G - 1) * H + (H - 1) := by ring
  rw [Cong, this]
  exact dvd_add (hG.mul_right _) hH

theorem Cong.one (m : ℕ) : Cong m 1 := by simp [Cong]

theorem Cong.prod {m : ℕ} {ι : Type*} (s : Finset ι) {g : ι → PowerSeries ℤ} (hg : ∀ i ∈ s, Cong m (g i)) :
    Cong m (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cong.one m
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (hg i (Finset.mem_insert_self i s)).mul (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))

theorem Cong.one_sub_X_pow {m n : ℕ} (hn : m + 1 ≤ n + 1) : Cong m (1 - PowerSeries.X ^ (n + 1)) := by
  rw [Cong, sub_sub_cancel_left, dvd_neg]
  exact pow_dvd_pow _ hn

theorem coeff_mul_of_cong {m : ℕ} {G : PowerSeries ℤ} (hG : Cong m G) (H : PowerSeries ℤ) :
    PowerSeries.coeff m (H * G) = PowerSeries.coeff m H := by
  obtain ⟨K, hK⟩ := hG
  have : G = 1 + PowerSeries.X ^ (m + 1) * K := by rw [← hK]; ring
  rw [this, mul_add, mul_one, map_add, ← mul_assoc, mul_comm H, mul_assoc, PowerSeries.coeff_X_pow_mul',
    if_neg (by omega), add_zero]

theorem coeff_prod_eq (m : ℕ) (s : Finset ℕ) (hs : Finset.range (m + 1) ⊆ s) :
    PowerSeries.coeff m (∏ n ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))) =
      PowerSeries.coeff m (∏ n ∈ Finset.range (m + 1), ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))) := by
  rw [← Finset.prod_sdiff hs, mul_comm]
  apply coeff_mul_of_cong
  apply Cong.prod
  intro n hn
  rw [Finset.mem_sdiff, Finset.mem_range, not_lt] at hn
  exact Cong.one_sub_X_pow (by omega)

open Filter Topology in
open scoped PowerSeries.WithPiTopology in
theorem coeff_etaProd_eq (m : ℕ) :
    PowerSeries.coeff m etaProd =
      PowerSeries.coeff m (∏ n ∈ Finset.range (m + 1), ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))) := by
  have hmult := PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ
  have h1 : Tendsto (fun s : Finset ℕ => ∏ n ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))) atTop
      (𝓝 etaProd) := hmult.hasProd
  have h2 := ((PowerSeries.WithPiTopology.continuous_coeff ℤ m).tendsto _).comp h1
  have h3 : Tendsto (fun s : Finset ℕ =>
      PowerSeries.coeff m (∏ n ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1)))) atTop
      (𝓝 (PowerSeries.coeff m (∏ n ∈ Finset.range (m + 1), ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (Finset.range (m + 1))] with s hs
    exact (coeff_prod_eq m s hs).symm
  exact tendsto_nhds_unique h2 h3

theorem coeff_etaProd_eq_coeff_prod (N m : ℕ) (hm : m < N) :
    PowerSeries.coeff m etaProd =
      PowerSeries.coeff m (∏ n ∈ Finset.range N, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))) := by
  rw [coeff_etaProd_eq]
  exact (coeff_prod_eq m (Finset.range N) (Finset.range_subset_range.mpr hm)).symm

theorem Rep.etaProd (N : ℕ) : Rep N (etaL N) etaProd := by
  have h := Rep.foldr (N := N) ((List.range N).map fun n => (facL N (n + 1), (1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1)))
    (fun p hp => by
      obtain ⟨n, -, rfl⟩ := List.mem_map.mp hp
      exact Rep.fac N (n + 1))
  rw [List.map_map, List.map_map] at h
  have h' : Rep N (etaL N) (((List.range N).map fun n => (1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1)).prod) := h
  intro m hm
  have hr : Finset.range N = (List.range N).toFinset := by ext; simp
  rw [coeff_etaProd_eq_coeff_prod N m hm, hr, List.prod_toFinset _ List.nodup_range]
  exact h' m hm

theorem Rep.S (N a b c e : ℕ) :
    Rep N (mulL N (XpowL N e) (mulL N (mulL N (powL N (etaL N) a) (expandL N 2 (powL N (etaL N) b)))
      (expandL N 4 (powL N (etaL N) c)))) (S a b c e) :=
  (Rep.Xpow N e).mul ((((Rep.etaProd N).pow a).mul (Rep.expand two_ne_zero ((Rep.etaProd N).pow b))).mul
    (Rep.expand (by norm_num) ((Rep.etaProd N).pow c)))

end ARails
p2m_reactivate "P2MW.S_ModularForm_eta_pow_twentyfour_eq.ModularCurve.ARails"
end ModularCurve
p2m_reactivate "P2MW.S_ModularForm_eta_pow_twentyfour_eq.ModularCurve.ARails P2MW.S_ModularForm_eta_pow_twentyfour_eq.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "etaProd hasSum_coeff_etaProd_pow hasSum_qParam_mul Gamma0_index dedekindPsi_prime_pow"
p2m_open "ModularCurve"
namespace A1proof
open ARails
open scoped MatrixGroups
local notation "𝕢" => Function.Periodic.qParam

theorem exists_forms :
    ∃ f₁ f₂ f₃ : ModularForm (CongruenceSubgroup.Gamma0 4) 12,
      (∀ z : UpperHalfPlane, f₁ z = ModularForm.eta (z : ℂ) ^ 0 * ModularForm.eta (2 * (z : ℂ)) ^ 24 *
        ModularForm.eta (4 * (z : ℂ)) ^ 0) ∧
      (∀ z : UpperHalfPlane, f₂ z = ModularForm.eta (z : ℂ) ^ 16 * ModularForm.eta (2 * (z : ℂ)) ^ 0 *
        ModularForm.eta (4 * (z : ℂ)) ^ 8) ∧
      (∀ z : UpperHalfPlane, f₃ z = ModularForm.eta (z : ℂ) ^ 8 * ModularForm.eta (2 * (z : ℂ)) ^ 0 *
        ModularForm.eta (4 * (z : ℂ)) ^ 16) := by
  obtain ⟨g₁, hg₁⟩ := CuspForm.exists_gamma0_four_apply_eq_eta_pow_mul 0 24 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨g₂, hg₂⟩ := CuspForm.exists_gamma0_four_apply_eq_eta_pow_mul 16 0 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨g₃, hg₃⟩ := CuspForm.exists_gamma0_four_apply_eq_eta_pow_mul 8 0 16 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨(toMF g₁).mcast (by norm_num) rfl, (toMF g₂).mcast (by norm_num) rfl, (toMF g₃).mcast (by norm_num) rfl,
    fun z => ?_, fun z => ?_, fun z => ?_⟩
  · exact hg₁ z
  · exact hg₂ z
  · exact hg₃ z

def L₁ : List ℤ := mulL 7 (XpowL 7 2) (mulL 7 (mulL 7 (powL 7 (etaL 7) 0) (expandL 7 2 (powL 7 (etaL 7) 24)))
  (expandL 7 4 (powL 7 (etaL 7) 0)))
def L₂ : List ℤ := mulL 7 (XpowL 7 2) (mulL 7 (mulL 7 (powL 7 (etaL 7) 16) (expandL 7 2 (powL 7 (etaL 7) 0)))
  (expandL 7 4 (powL 7 (etaL 7) 8)))
def L₃ : List ℤ := mulL 7 (XpowL 7 3) (mulL 7 (mulL 7 (powL 7 (etaL 7) 8) (expandL 7 2 (powL 7 (etaL 7) 0)))
  (expandL 7 4 (powL 7 (etaL 7) 16)))

theorem rep₁ : Rep 7 L₁ (S 0 24 0 2) := Rep.S 7 0 24 0 2
theorem rep₂ : Rep 7 L₂ (S 16 0 8 2) := Rep.S 7 16 0 8 2
theorem rep₃ : Rep 7 L₃ (S 8 0 16 3) := Rep.S 7 8 0 16 3

set_option maxRecDepth 20000 in
theorem lists_cancel : ∀ m, m < 7 → L₁.getD m 0 - L₂.getD m 0 - 16 * L₃.getD m 0 = 0 := by decide +kernel

theorem zform (z : UpperHalfPlane) :
    ModularForm.eta (2 * (z : ℂ)) ^ 24 =
      ModularForm.eta (z : ℂ) ^ 16 * ModularForm.eta (4 * (z : ℂ)) ^ 8 +
        16 * ModularForm.eta (z : ℂ) ^ 8 * ModularForm.eta (4 * (z : ℂ)) ^ 16 := by
  obtain ⟨f₁, f₂, f₃, h₁, h₂, h₃⟩ := exists_forms
  let F : ModularForm (CongruenceSubgroup.Gamma0 4) 12 := f₁ - f₂ - (16 : ℂ) • f₃
  have hF : ∀ z : UpperHalfPlane, F z = f₁ z - f₂ z - 16 * f₃ z := fun z => rfl
  have hcoeff : ∀ n : ℕ, n < 7 → (UpperHalfPlane.qExpansion 1 F).coeff n = 0 := by
    intro n hn
    have hs : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ =>
        (((PowerSeries.coeff m (S 0 24 0 2) : ℤ) : ℂ) - ((PowerSeries.coeff m (S 16 0 8 2) : ℤ) : ℂ) -
          16 * ((PowerSeries.coeff m (S 8 0 16 3) : ℤ) : ℂ)) • 𝕢 1 (τ : ℂ) ^ m) (F τ) := by
      intro τ
      have := ((hasSum_etaProduct 0 24 0 2 (by norm_num) τ).sub (hasSum_etaProduct 16 0 8 2 (by norm_num) τ)).sub
        ((hasSum_etaProduct 8 0 16 3 (by norm_num) τ).mul_left 16)
      rw [hF, h₁, h₂, h₃]
      convert this using 1 <;> try with_reducible_and_instances rfl
      · funext m; simp only [smul_eq_mul]; ring
    rw [← ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods_Gamma0 4) (f := F) hs n,
      ← rep₁ n hn, ← rep₂ n hn, ← rep₃ n hn]
    norm_cast
    exact lists_cancel n hn
  have hF0 : F = 0 := by
    refine ModularForm.sturm_bound_Gamma0 4 F (fun n hn => hcoeff n ?_)
    rw [index_Gamma0_four] at hn
    norm_num at hn
    omega
  have := congrArg (fun G : ModularForm (CongruenceSubgroup.Gamma0 4) 12 => G z) hF0
  simp only [hF, h₁, h₂, h₃, ModularForm.zero_apply, pow_zero, mul_one, one_mul] at this
  linear_combination this

theorem main (τ : UpperHalfPlane) :
    ModularForm.eta (τ : ℂ) ^ 24 =
      ModularForm.eta ((τ : ℂ) / 2) ^ 16 * ModularForm.eta (2 * (τ : ℂ)) ^ 8 +
        16 * ModularForm.eta ((τ : ℂ) / 2) ^ 8 * ModularForm.eta (2 * (τ : ℂ)) ^ 16 := by
  have hz : 0 < ((τ : ℂ) / 2).im := by
    rw [Complex.div_ofNat_im]
    exact div_pos τ.im_pos two_pos
  have h := zform ⟨(τ : ℂ) / 2, hz⟩
  have e1 : (2 : ℂ) * ((τ : ℂ) / 2) = τ := by ring
  have e2 : (4 : ℂ) * ((τ : ℂ) / 2) = 2 * τ := by ring
  simp only [UpperHalfPlane.coe_mk, e1, e2] at h
  exact h

end A1proof
p2m_reactivate "P2MW.S_ModularForm_eta_pow_twentyfour_eq.ModularCurve.ARails P2MW.S_ModularForm_eta_pow_twentyfour_eq.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularForm_eta_pow_twentyfour_eq.ModularCurve.ARails P2MW.S_ModularForm_eta_pow_twentyfour_eq.ModularCurve"

theorem solution (τ : UpperHalfPlane) :
    ModularForm.eta (τ : ℂ) ^ 24 =
      ModularForm.eta ((τ : ℂ) / 2) ^ 16 * ModularForm.eta (2 * (τ : ℂ)) ^ 8 +
        16 * ModularForm.eta ((τ : ℂ) / 2) ^ 8 * ModularForm.eta (2 * (τ : ℂ)) ^ 16 :=
  ModularCurve.A1proof.main τ

end S_ModularForm_eta_pow_twentyfour_eq
end P2MW
export P2MW.S_ModularForm_eta_pow_twentyfour_eq (solution)
