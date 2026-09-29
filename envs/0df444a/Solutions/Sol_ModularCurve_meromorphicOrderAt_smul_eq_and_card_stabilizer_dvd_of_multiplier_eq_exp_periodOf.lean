-- Prove2me | solution 1 for ModularCurve.meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp_periodOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/be6e525c-cf34-5ca3-8276-1e5df84365e3

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitiveOf
import Theorems.Thm_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp_periodOf

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Filter
open scoped MatrixGroups Topology

namespace ModularCurve
p2m_export "ModularCurve" "periodOf HasEquivariantPrimitiveOf period Period.IsEquivariantPrimitive exists_hasEquivariantPrimitiveOf periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf"
namespace EllipticOrderProofOf
p2m_open "ModularCurve"

def J (γ : SL(2, ℤ)) (z : ℂ) : ℂ := denom (γ : GL (Fin 2) ℝ) z

def mob (γ : SL(2, ℤ)) (z : ℂ) : ℂ := num (γ : GL (Fin 2) ℝ) z / denom (γ : GL (Fin 2) ℝ) z

theorem J_apply (γ : SL(2, ℤ)) (z : ℂ) :
    J γ z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  simp [J, denom]

theorem num_apply (γ : SL(2, ℤ)) (z : ℂ) :
    num (γ : GL (Fin 2) ℝ) z = ((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ) := by
  simp [num]

theorem mob_apply (γ : SL(2, ℤ)) (z : ℂ) :
    mob γ z = (((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ)) / J γ z := by
  rw [mob, num_apply]; rfl

theorem det_one (γ : SL(2, ℤ)) :
    ((γ 0 0 : ℤ) : ℂ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
  have := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at this
  exact_mod_cast this

theorem J_ne_zero (γ : SL(2, ℤ)) {z : ℂ} (hz : z.im ≠ 0) : J γ z ≠ 0 :=
  denom_ne_zero_of_im _ hz

theorem J_coe_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) : J γ τ ≠ 0 := J_ne_zero γ τ.im_ne_zero

theorem coe_smul_eq_mob (γ : SL(2, ℤ)) (τ : ℍ) : ((γ • τ : ℍ) : ℂ) = mob γ τ := by
  rw [ModularGroup.sl_moeb, coe_smul_of_det_pos (by simp)]
  rfl

theorem mob_sub_mob (γ : SL(2, ℤ)) {z w : ℂ} (hz : J γ z ≠ 0) (hw : J γ w ≠ 0) :
    mob γ z - mob γ w = (z - w) / (J γ z * J γ w) := by
  rw [mob_apply, mob_apply, div_sub_div _ _ hz hw]
  congr 1
  rw [J_apply, J_apply]
  linear_combination (z - w) * det_one γ

theorem continuousAt_J (γ : SL(2, ℤ)) (z : ℂ) : ContinuousAt (J γ) z := by
  have : Continuous (J γ) := by
    simp only [funext (J_apply γ)]
    fun_prop
  exact this.continuousAt

theorem analyticAt_J (γ : SL(2, ℤ)) (z : ℂ) : AnalyticAt ℂ (J γ) z := by
  simp only [funext (J_apply γ)]
  fun_prop

theorem analyticAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : J γ z ≠ 0) : AnalyticAt ℂ (mob γ) z := by
  simp only [funext (mob_apply γ)]
  exact AnalyticAt.div (by fun_prop) (analyticAt_J γ z) hz

theorem continuousAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : J γ z ≠ 0) : ContinuousAt (mob γ) z :=
  (analyticAt_mob γ hz).continuousAt

theorem tendsto_mob_nhdsNE (γ : SL(2, ℤ)) {τ : ℂ} (hτ : J γ τ ≠ 0) (hfix : mob γ τ = τ) :
    Tendsto (mob γ) (𝓝[≠] τ) (𝓝[≠] τ) := by
  have hc : ContinuousAt (mob γ) τ := continuousAt_mob γ hτ
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have := hc.tendsto
    rw [hfix] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have hJ : ∀ᶠ z in 𝓝[≠] τ, J γ z ≠ 0 :=
      eventually_nhdsWithin_of_eventually_nhds ((continuousAt_J γ τ).eventually_ne hτ)
    have hne : ∀ᶠ z in 𝓝[≠] τ, z ≠ τ := eventually_nhdsWithin_of_forall fun z hz => hz
    filter_upwards [hJ, hne] with z hJz hz
    change mob γ z ≠ τ
    intro h
    have := mob_sub_mob γ hJz hτ
    rw [hfix, h, sub_self] at this
    have h2 : (z - τ) / (J γ z * J γ τ) ≠ 0 :=
      div_ne_zero (sub_ne_zero.2 hz) (mul_ne_zero hJz hτ)
    exact h2 this.symm

theorem hasDerivAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : J γ z ≠ 0) :
    HasDerivAt (mob γ) (J γ z ^ 2)⁻¹ z := by
  have h1 : HasDerivAt (fun w : ℂ => ((γ 0 0 : ℤ) : ℂ) * w + ((γ 0 1 : ℤ) : ℂ))
      ((γ 0 0 : ℤ) : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul ((γ 0 0 : ℤ) : ℂ)).add_const ((γ 0 1 : ℤ) : ℂ)
  have h2 : HasDerivAt (J γ) ((γ 1 0 : ℤ) : ℂ) z := by
    rw [funext (J_apply γ)]
    simpa using ((hasDerivAt_id z).const_mul ((γ 1 0 : ℤ) : ℂ)).add_const ((γ 1 1 : ℤ) : ℂ)
  have h3 := h1.div h2 hz
  rw [funext (mob_apply γ)]
  convert h3 using 1
  all_goals try rfl
  have hd := det_one γ
  rw [J_apply] at hz ⊢
  field_simp
  linear_combination (-1) * hd

theorem deriv_mob_ne_zero (γ : SL(2, ℤ)) {z : ℂ} (hz : J γ z ≠ 0) : deriv (mob γ) z ≠ 0 := by
  rw [(hasDerivAt_mob γ hz).deriv]
  exact inv_ne_zero (pow_ne_zero _ hz)

theorem meromorphicOrderAt_comp_mob (f : ℂ → ℂ) (γ : SL(2, ℤ)) {z : ℂ} (hz : J γ z ≠ 0) :
    meromorphicOrderAt (f ∘ mob γ) z = meromorphicOrderAt f (mob γ z) :=
  meromorphicOrderAt_comp_of_deriv_ne_zero (analyticAt_mob γ hz) (deriv_mob_ne_zero γ hz)

theorem eventually_comp_mob (F : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    ∀ᶠ z in 𝓝 (τ : ℂ), F (ofComplex (mob γ z)) = F (γ • ofComplex z) := by
  have hpos : ∀ᶠ z in 𝓝 (τ : ℂ), 0 < z.im :=
    Complex.continuous_im.continuousAt.eventually (lt_mem_nhds τ.im_pos)
  filter_upwards [hpos] with z hz
  have h1 : ofComplex z = ⟨z, hz⟩ := ofComplex_apply_of_im_pos hz
  rw [h1]
  have h2 : mob γ z = ((γ • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) := (coe_smul_eq_mob γ ⟨z, hz⟩).symm
  rw [h2, ofComplex_apply]

theorem meromorphicOrderAt_smul (F : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) ((γ • τ : ℍ) : ℂ) =
      meromorphicOrderAt (fun z : ℂ => F (γ • ofComplex z)) (τ : ℂ) := by
  rw [coe_smul_eq_mob, ← meromorphicOrderAt_comp_mob _ γ (J_coe_ne_zero γ τ)]
  apply meromorphicOrderAt_congr
  exact eventually_nhdsWithin_of_eventually_nhds (eventually_comp_mob F γ τ)

theorem meromorphicOrderAt_smul_of_mul (F : ℍ → ℂ) (γ : SL(2, ℤ)) {c : ℂ} (hc : c ≠ 0)
    (h : ∀ w : ℍ, F (γ • w) = c * F w) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) ((γ • τ : ℍ) : ℂ) =
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) := by
  rw [meromorphicOrderAt_smul]
  simp only [h]
  exact meromorphicOrderAt_mul_of_ne_zero (f := fun z : ℂ => F (ofComplex z))
    (g := fun _ => c) analyticAt_const hc

theorem J_sq_zpow_eq_one {f : ℂ → ℂ} {τ : ℂ} (γ : SL(2, ℤ)) (hτ : J γ τ ≠ 0)
    (hfix : mob γ τ = τ) (hinv : ∀ᶠ z in 𝓝[≠] τ, f (mob γ z) = f z)
    (hf : MeromorphicAt f τ) {n : ℤ} (hn : meromorphicOrderAt f τ = n) :
    (J γ τ * J γ τ) ^ n = 1 := by
  obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn
  have hmt := tendsto_mob_nhdsNE γ hτ hfix

  have hfg' : ∀ᶠ z in 𝓝[≠] τ, f (mob γ z) = (mob γ z - τ) ^ n • g (mob γ z) :=
    hmt.eventually hfg
  have hJ : ∀ᶠ z in 𝓝[≠] τ, J γ z ≠ 0 :=
    eventually_nhdsWithin_of_eventually_nhds ((continuousAt_J γ τ).eventually_ne hτ)
  have hne : ∀ᶠ z in 𝓝[≠] τ, z ≠ τ := eventually_nhdsWithin_of_forall fun z hz => hz

  have hcmp : ∀ᶠ z in 𝓝[≠] τ, g z = ((J γ z * J γ τ)⁻¹) ^ n * g (mob γ z) := by
    filter_upwards [hfg, hfg', hinv, hJ, hne] with z h1 h2 h3 hJz hz
    have hsub : mob γ z - τ = (z - τ) / (J γ z * J γ τ) := by
      rw [← mob_sub_mob γ hJz hτ, hfix]
    rw [h3, h1, hsub, smul_eq_mul, smul_eq_mul, div_eq_mul_inv, mul_zpow, mul_assoc] at h2
    have hzn : (z - τ) ^ n ≠ 0 := zpow_ne_zero n (sub_ne_zero.2 hz)
    exact mul_left_cancel₀ hzn h2

  have hL : Tendsto g (𝓝[≠] τ) (𝓝 (g τ)) := hg.continuousAt.continuousWithinAt.tendsto
  have hR : Tendsto (fun z => ((J γ z * J γ τ)⁻¹) ^ n * g (mob γ z)) (𝓝[≠] τ)
      (𝓝 (((J γ τ * J γ τ)⁻¹) ^ n * g τ)) := by
    have h1 : ContinuousAt (fun z => ((J γ z * J γ τ)⁻¹) ^ n) τ := by
      refine ContinuousAt.zpow₀ ?_ n (Or.inl (inv_ne_zero (mul_ne_zero hτ hτ)))
      exact ((continuousAt_J γ τ).mul continuousAt_const).inv₀ (mul_ne_zero hτ hτ)
    have h2 : ContinuousAt (fun z => g (mob γ z)) τ := by
      have hgc : ContinuousAt g (mob γ τ) := by rw [hfix]; exact hg.continuousAt
      exact ContinuousAt.comp hgc (continuousAt_mob γ hτ)
    have h3 : ContinuousAt (fun z => ((J γ z * J γ τ)⁻¹) ^ n * g (mob γ z)) τ := h1.mul h2
    have := h3.tendsto
    simp only [hfix] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim := tendsto_nhds_unique (hR.congr' (hcmp.mono fun z hz => hz.symm)) hL

  have h1 : ((J γ τ * J γ τ)⁻¹) ^ n = 1 := by
    have := mul_right_cancel₀ hg0 (hlim.trans (one_mul (g τ)).symm)
    exact this
  rwa [inv_zpow, inv_eq_one] at h1

section Group

variable {Γ : Subgroup SL(2, ℤ)}

theorem finite_setOf_smul_eq (τ : ℍ) : {g : SL(2, ℤ) | g • τ = τ}.Finite := by
  have h := ProperlyDiscontinuousSMul.finite_stabilizer' (↥𝒮ℒ) τ
  let φ : SL(2, ℤ) → ↥𝒮ℒ := (Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
  have hφ : Function.Injective φ := by
    intro a b hab
    have := congrArg Subtype.val hab
    simpa [φ] using this
  have hset : {g : SL(2, ℤ) | g • τ = τ} = φ ⁻¹' {s : ↥𝒮ℒ | s • τ = τ} := by
    ext g
    rfl
  rw [hset]
  exact h.preimage hφ.injOn

scoped instance finite_stabilizer (τ : ℍ) :
    Finite (MulAction.stabilizer (Γ) τ) := by
  have h := finite_setOf_smul_eq τ
  have : Set.Finite ((MulAction.stabilizer (Γ) τ :
      Set (Γ))) := by
    have hsub : (MulAction.stabilizer (Γ) τ :
        Set (Γ)) = Subtype.val ⁻¹' {g : SL(2, ℤ) | g • τ = τ} := by
      ext γ
      simp [MulAction.mem_stabilizer_iff]
      rfl
    rw [hsub]
    exact h.preimage Subtype.val_injective.injOn
  exact this.to_subtype

theorem smul_eq_of_mem_stabilizer {γ : Γ} {τ : ℍ}
    (h : γ ∈ MulAction.stabilizer (Γ) τ) : (γ : SL(2, ℤ)) • τ = τ :=
  h

theorem mob_eq_of_mem_stabilizer {γ : Γ} {τ : ℍ}
    (h : γ ∈ MulAction.stabilizer (Γ) τ) :
    mob (γ : SL(2, ℤ)) τ = τ := by
  rw [← coe_smul_eq_mob, smul_eq_of_mem_stabilizer h]

theorem J_mul_of_smul_eq (γ δ : SL(2, ℤ)) {τ : ℍ} (hδ : δ • τ = τ) :
    J (γ * δ) τ = J γ τ * J δ τ := by
  have h := denom_cocycle (γ : GL (Fin 2) ℝ) (δ : GL (Fin 2) ℝ) τ.im_ne_zero
  have hmob : num (δ : GL (Fin 2) ℝ) τ / denom (δ : GL (Fin 2) ℝ) τ = τ := by
    have := coe_smul_eq_mob δ τ
    rw [hδ] at this
    exact this.symm
  rw [hmob] at h
  simpa [J] using h

def jChar (τ : ℍ) : MulAction.stabilizer (Γ) τ →* ℂˣ where
  toFun γ := Units.mk0 (J ((γ : Γ) : SL(2, ℤ)) τ)
    (J_coe_ne_zero _ τ)
  map_one' := by
    ext
    simp [J_apply]
  map_mul' γ δ := by
    ext
    simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul]
    exact J_mul_of_smul_eq _ _ (smul_eq_of_mem_stabilizer δ.prop)

@[scoped simp] theorem jChar_apply (τ : ℍ) (γ : MulAction.stabilizer (Γ) τ) :
    ((jChar τ γ : ℂˣ) : ℂ) = J ((γ : Γ) : SL(2, ℤ)) τ := rfl

theorem eq_one_of_J_eq_one {γ : SL(2, ℤ)} {τ : ℍ} (hfix : γ • τ = τ) (hJ : J γ τ = 1) :
    γ = 1 := by
  rw [J_apply] at hJ
  have hc : γ 1 0 = 0 := by
    have := congrArg Complex.im hJ
    simpa [τ.im_ne_zero] using this
  have hd : γ 1 1 = 1 := by
    have := congrArg Complex.re hJ
    simp [hc] at this
    exact_mod_cast this
  have ha : γ 0 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two, hc, hd] at this
    simpa using this
  have hb : γ 0 1 = 0 := by
    have h := congrArg (fun w : ℍ => (w : ℂ)) hfix
    simp only [coe_smul_eq_mob, mob_apply, J_apply, hc, hd, ha] at h
    push_cast at h
    have : ((γ 0 1 : ℤ) : ℂ) = 0 := by linear_combination h
    exact_mod_cast this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

theorem jChar_injective (τ : ℍ) : Function.Injective (jChar (Γ := Γ) τ) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  have hJ : J ((γ : Γ) : SL(2, ℤ)) τ = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) hγ
    simpa using this
  have h1 : ((γ : Γ) : SL(2, ℤ)) = 1 :=
    eq_one_of_J_eq_one (smul_eq_of_mem_stabilizer γ.prop) hJ
  ext : 2
  exact_mod_cast h1

scoped instance isCyclic_stabilizer (τ : ℍ) :
    IsCyclic (MulAction.stabilizer (Γ) τ) :=
  isCyclic_of_injective_ringHom ((Units.coeHom ℂ).comp (jChar τ))
    (Units.val_injective.comp (jChar_injective τ))

theorem card_stabilizer_dvd {τ : ℍ} {n : ℤ}
    (h : ∀ γ : MulAction.stabilizer (Γ) τ,
      (J ((γ : Γ) : SL(2, ℤ)) τ *
        J ((γ : Γ) : SL(2, ℤ)) τ) ^ n = 1) :
    (Nat.card (MulAction.stabilizer (Γ) τ) : ℤ) ∣ 2 * n := by
  obtain ⟨g₀, hg₀⟩ :=
    IsCyclic.exists_generator (α := MulAction.stabilizer (Γ) τ)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg₀, ← orderOf_injective (jChar τ)
    (jChar_injective τ) g₀, orderOf_dvd_iff_zpow_eq_one]
  ext
  rw [Units.val_zpow_eq_zpow_val, jChar_apply, zpow_mul, Units.val_one]
  simpa [zpow_two, sq] using h g₀

end Group

section Multiplier

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

theorem period_eq_sub (k : CuspForm Γ 2) {Φ : ℍ → ℂ}
    (hΦ : ModularCurve.HasEquivariantPrimitiveOf Γ k Φ) (γ : Γ) (τ : ℍ) :
    ModularCurve.periodOf Γ γ k = Φ ((γ : SL(2, ℤ)) • τ) - Φ τ := by
  rw [ModularCurve.periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf Γ k hΦ γ]
  have hequiv : ModularCurve.Period.IsEquivariantPrimitive Γ Φ := hΦ.2.2.1
  rw [hequiv.sub_eq_period γ UpperHalfPlane.I, ← hequiv.sub_eq_period γ τ]

theorem period_eq_zero_of_isOfFinOrder (k : CuspForm Γ 2) {γ : Γ}
    (hγ : IsOfFinOrder γ) : ModularCurve.periodOf Γ γ k = 0 := by
  obtain ⟨Φ, hΦ⟩ := ModularCurve.exists_hasEquivariantPrimitiveOf Γ k

  have hadd : ∀ a b : Γ, ModularCurve.periodOf Γ (a * b) k =
      ModularCurve.periodOf Γ a k + ModularCurve.periodOf Γ b k := by
    intro a b
    rw [period_eq_sub k hΦ (a * b) UpperHalfPlane.I,
      period_eq_sub k hΦ a ((b : SL(2, ℤ)) • UpperHalfPlane.I),
      period_eq_sub k hΦ b UpperHalfPlane.I, Subgroup.coe_mul, mul_smul]
    ring
  have hpow : ∀ n : ℕ, ModularCurve.periodOf Γ (γ ^ n) k = n * ModularCurve.periodOf Γ γ k := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, period_eq_sub k hΦ 1 UpperHalfPlane.I, Subgroup.coe_one, one_smul]
      simp
    | succ n ih => rw [pow_succ, hadd, ih]; push_cast; ring
  obtain ⟨n, hn, hγn⟩ := hγ.exists_pow_eq_one
  have h := hpow n
  rw [hγn, period_eq_sub k hΦ 1 UpperHalfPlane.I, Subgroup.coe_one, one_smul, sub_self] at h
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  exact (mul_eq_zero.mp h.symm).resolve_left hn'

theorem isOfFinOrder_of_mem_stabilizer {γ : Γ} {τ : ℍ}
    (h : γ ∈ MulAction.stabilizer Γ τ) : IsOfFinOrder γ := by
  have : IsOfFinOrder (⟨γ, h⟩ : MulAction.stabilizer Γ τ) := isOfFinOrder_of_finite _
  exact (MulAction.stabilizer Γ τ).subtype.isOfFinOrder this

theorem apply_smul_eq_of_mem_stabilizer (F : ℍ → ℂ) (k : CuspForm Γ 2)
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) * F τ)
    {γ : Γ} {τ₀ : ℍ} (h : γ ∈ MulAction.stabilizer Γ τ₀) (τ : ℍ) :
    F ((γ : SL(2, ℤ)) • τ) = F τ := by
  rw [hχ γ τ, period_eq_zero_of_isOfFinOrder k (isOfFinOrder_of_mem_stabilizer h)]
  simp

end Multiplier

section Assembly

variable {Γ : Subgroup SL(2, ℤ)}

theorem eventually_comp_mob_eq (F : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ)
    (hinv : ∀ w : ℍ, F (γ • w) = F w) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), F (ofComplex (mob γ z)) = F (ofComplex z) := by
  have him : ∀ᶠ z in 𝓝 (τ : ℂ), 0 < z.im :=
    Complex.continuous_im.continuousAt.eventually (lt_mem_nhds τ.im_pos)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds him] with z hz
  have h1 : mob γ z = ((γ • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) := (coe_smul_eq_mob γ ⟨z, hz⟩).symm
  rw [h1, ofComplex_apply, hinv, ofComplex_apply_of_im_pos hz]

theorem card_stabilizer_dvd_of_invariant (F : ℍ → ℂ) (τ : ℍ)
    (hF : MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) {n : ℤ}
    (hn : meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = n)
    (hinv : ∀ γ ∈ MulAction.stabilizer (Γ) τ,
      ∀ w : ℍ, F ((γ : SL(2, ℤ)) • w) = F w) :
    (Nat.card (MulAction.stabilizer (Γ) τ) : ℤ) ∣ 2 * n := by
  refine card_stabilizer_dvd (Γ := Γ) (τ := τ) (n := n) fun γ => ?_
  exact J_sq_zpow_eq_one (f := fun z : ℂ => F (ofComplex z)) _ (J_coe_ne_zero _ τ)
    (mob_eq_of_mem_stabilizer γ.prop) (eventually_comp_mob_eq F _ τ (hinv _ γ.prop)) hF hn

end Assembly

end ModularCurve.EllipticOrderProofOf
p2m_reactivate "P2MW.S_ModularCurve_meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp_periodOf.ModularCurve P2MW.S_ModularCurve_meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp_periodOf.ModularCurve.EllipticOrderProofOf"
p2m_reactivate "P2MW.S_ModularCurve_meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp_periodOf.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp_periodOf.ModularCurve P2MW.S_ModularCurve_meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp_periodOf.ModularCurve.EllipticOrderProofOf"

open UpperHalfPlane
open scoped MatrixGroups Topology

open ModularCurve.EllipticOrderProofOf in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (F : ℍ → ℂ) (k : CuspForm (Γ) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) * F τ) :
    (∀ (γ : Γ) (τ : ℍ),
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) =
        meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) ∧
    (∀ (τ : ℍ) (n : ℤ),
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) →
        (Nat.card (MulAction.stabilizer (Γ) τ) : ℤ) ∣ 2 * n) := by
  refine ⟨fun γ τ => ?_, fun τ n hn => ?_⟩
  · exact meromorphicOrderAt_smul_of_mul F (γ : SL(2, ℤ)) (Complex.exp_ne_zero _) (hχ γ) τ
  · exact card_stabilizer_dvd_of_invariant F τ (hF τ) hn
      fun γ hγ w => apply_smul_eq_of_mem_stabilizer F k hχ hγ w

end S_ModularCurve_meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp_periodOf
end P2MW
export P2MW.S_ModularCurve_meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp_periodOf (solution)
