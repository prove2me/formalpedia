-- Prove2me | solution 1 for ModularCurve.exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/7436b5a3-7c4b-5ad9-acb7-f8981a7cf371

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Definitions.Def_Gamma0CoeffCohomology
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitive
import Theorems.Thm_ModularCurve_period_apply_eq_sub_of_hasEquivariantPrimitive
import Theorems.Thm_HeckeEis_existsUnique_coeffCocycles_sl2z_apply_S_ST_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "period Period.IsParabolicHom HasEquivariantPrimitive exists_hasEquivariantPrimitive period_apply_eq_sub_of_hasEquivariantPrimitive"
namespace PoincareDualSurjectivity
p2m_open "ModularCurve"

open scoped MatrixGroups

section Algebra

variable {N : ℕ}

local notation "Γ" => CongruenceSubgroup.Gamma0 N
local notation "Q" => SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N

theorem gam_mem (M : SL(2, ℤ)) (q : Q) :
    (Quotient.out (M • q))⁻¹ * M * Quotient.out q ∈ Γ := by
  rw [mul_assoc, ← QuotientGroup.eq, QuotientGroup.out_eq', ← MulAction.Quotient.coe_smul_out,
    smul_eq_mul]

def gam (M : SL(2, ℤ)) (q : Q) : Γ := ⟨_, gam_mem M q⟩

@[scoped simp] theorem coe_gam (M : SL(2, ℤ)) (q : Q) :
    ((gam M q : Γ) : SL(2, ℤ)) = (Quotient.out (M • q))⁻¹ * M * Quotient.out q := rfl

theorem S_pow_two : ModularGroup.S ^ 2 = -1 := by
  ext1
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_two, ModularGroup.S_mul_S_eq]
  simp

theorem ST_pow_three : (ModularGroup.S * ModularGroup.T) ^ 3 = -1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S,
    ModularGroup.coe_T]
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem neg_one_mem : (-1 : SL(2, ℤ)) ∈ Γ := by
  simp [CongruenceSubgroup.Gamma0_mem]

theorem neg_one_smul (q : Q) : (-1 : SL(2, ℤ)) • q = q := by
  induction q using QuotientGroup.induction_on with
  | H σ =>
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
    simp

theorem neg_smul (M : SL(2, ℤ)) (q : Q) : (-M) • q = M • q := by
  rw [← neg_one_mul, mul_smul, neg_one_smul]

theorem S_smul_S_smul (q : Q) : ModularGroup.S • ModularGroup.S • q = q := by
  rw [← mul_smul, ← pow_two, S_pow_two, neg_one_smul]

theorem S_inv_smul (q : Q) : ModularGroup.S⁻¹ • q = ModularGroup.S • q := by
  rw [inv_smul_eq_iff, S_smul_S_smul]

theorem S_inv : ModularGroup.S⁻¹ = -ModularGroup.S := by
  rw [inv_eq_iff_mul_eq_one, mul_neg, ← pow_two, S_pow_two, neg_neg]

theorem ST_inv_smul3 (q : Q) :
    (ModularGroup.S * ModularGroup.T)⁻¹ • (ModularGroup.S * ModularGroup.T)⁻¹ •
      (ModularGroup.S * ModularGroup.T)⁻¹ • q = q := by
  rw [← mul_smul, ← mul_smul, ← mul_inv_rev, ← mul_inv_rev, ← pow_three, ST_pow_three,
    show (-1 : SL(2, ℤ))⁻¹ = -1 by simp, neg_one_smul]

def q0 : Q := ((1 : SL(2, ℤ)) : Q)

theorem smul_q0 (g : SL(2, ℤ)) : g • (q0 : Q) = (g : Q) := by
  rw [q0, MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]

theorem smul_q0_of_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) : γ • (q0 : Q) = q0 := by
  rw [smul_q0, q0, QuotientGroup.eq, mul_one]
  exact inv_mem hγ

theorem out_smul_q0 (q : Q) : Quotient.out q • (q0 : Q) = q := by
  rw [smul_q0, QuotientGroup.out_eq']

theorem smul_eq_of_conj_mem {M β : SL(2, ℤ)} (h : M * β * M⁻¹ ∈ Γ) :
    β • M⁻¹ • (q0 : Q) = M⁻¹ • q0 := by
  have : β * M⁻¹ = M⁻¹ * (M * β * M⁻¹) := by group
  rw [← mul_smul, this, mul_smul, smul_q0_of_mem h]

def coind : Representation ℤ SL(2, ℤ) (Q → ℤ) where
  toFun M :=
    { toFun := fun f q => f (M⁻¹ • q)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext f q; simp
  map_mul' M M' := by
    ext f q
    simp [mul_smul]

@[scoped simp] theorem coind_apply (M : SL(2, ℤ)) (f : Q → ℤ) (q : Q) : coind M f q = f (M⁻¹ • q) := rfl

structure Cocycle (N : ℕ) where
  z : SL(2, ℤ) → (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) → ℤ
  cocycle : ∀ g h, z (g * h) = z g + coind g (z h)

theorem exists_cocycle (c : Q → ℤ) :
    ∃ Z : Cocycle N, Z.z ModularGroup.S = 0 ∧
      Z.z (ModularGroup.S * ModularGroup.T) = coind (ModularGroup.S * ModularGroup.T) c - c := by
  have h3 : ∀ f : Q → ℤ, coind (ModularGroup.S * ModularGroup.T)
      (coind (ModularGroup.S * ModularGroup.T) (coind (ModularGroup.S * ModularGroup.T) f)) = f := by
    intro f
    ext q
    simp only [coind_apply]
    rw [ST_inv_smul3]
  have hy : coind (ModularGroup.S * ModularGroup.T) c - c
      + coind (ModularGroup.S * ModularGroup.T) (coind (ModularGroup.S * ModularGroup.T) c - c)
      + coind (ModularGroup.S * ModularGroup.T) (coind (ModularGroup.S * ModularGroup.T)
          (coind (ModularGroup.S * ModularGroup.T) c - c)) = 0 := by
    have e := h3 c
    ext q
    have e' := congr_fun e q
    simp only [coind_apply, Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at e' ⊢
    rw [e']
    ring
  obtain ⟨zz, hzS, hzU⟩ := (HeckeEis.existsUnique_coeffCocycles_sl2z_apply_S_ST_eq ℤ (Q → ℤ) coind 0
    _ (by simp) hy).exists
  exact ⟨⟨zz, (HeckeEis.mem_coeffCocycles_iff coind (zz : SL(2, ℤ) → Q → ℤ)).1 zz.2⟩, hzS, hzU⟩

namespace Cocycle

variable (Z : Cocycle N)

theorem mul_apply (g h : SL(2, ℤ)) (p : Q) : Z.z (g * h) p = Z.z g p + Z.z h (g⁻¹ • p) := by
  rw [Z.cocycle]; rfl

theorem one_apply (p : Q) : Z.z 1 p = 0 := by
  have h := Z.mul_apply 1 1 p
  rw [mul_one, inv_one, one_smul] at h
  linarith

theorem inv_apply (M : SL(2, ℤ)) (p : Q) : Z.z M⁻¹ p = -Z.z M (M • p) := by
  have h := Z.mul_apply M M⁻¹ (M • p)
  rw [mul_inv_cancel, Z.one_apply, inv_smul_smul] at h
  linarith

theorem neg_one_apply (p : Q) : Z.z (-1) p = 0 := by
  have h := Z.mul_apply (-1) (-1) p
  rw [show (-1 : SL(2, ℤ)) * -1 = 1 by simp, Z.one_apply,
    show (-1 : SL(2, ℤ))⁻¹ = -1 by simp, neg_one_smul] at h
  linarith

theorem eps_mul_apply {ε : SL(2, ℤ)} (hε : ε = 1 ∨ ε = -1) (M : SL(2, ℤ)) (p : Q) :
    Z.z (ε * M) p = Z.z M p := by
  rcases hε with rfl | rfl
  · rw [one_mul]
  · rw [Z.mul_apply, Z.neg_one_apply, show (-1 : SL(2, ℤ))⁻¹ = -1 by simp, neg_one_smul,
      zero_add]

def hom : Additive Γ →+ ℤ where
  toFun a := Z.z ((Additive.toMul a : Γ) : SL(2, ℤ)) q0
  map_zero' := by simp [Z.one_apply]
  map_add' a b := by
    simp only [toMul_add, Subgroup.coe_mul]
    rw [Z.mul_apply, smul_q0_of_mem (inv_mem (Additive.toMul a).2)]

theorem hom_apply (γ : Γ) : Z.hom (Additive.ofMul γ) = Z.z (γ : SL(2, ℤ)) q0 := rfl

def em (q : Q) : ℤ := -Z.z (Quotient.out q) q

theorem hom_gam (M : SL(2, ℤ)) (q : Q) :
    Z.hom (Additive.ofMul (gam M q)) = Z.z M (M • q) + Z.em (M • q) - Z.em q := by
  rw [hom_apply, coe_gam, Z.mul_apply, Z.mul_apply, Z.inv_apply, em, em]
  have h1 : (Quotient.out (M • q))⁻¹⁻¹ • (q0 : Q) = M • q := by rw [inv_inv, out_smul_q0]
  have h2 : ((Quotient.out (M • q))⁻¹ * M)⁻¹ • (q0 : Q) = q := by
    rw [mul_inv_rev, inv_inv, mul_smul, out_smul_q0, inv_smul_smul]
  rw [h1, h2, out_smul_q0]
  ring

theorem hom_conj (M β : SL(2, ℤ)) (h : M * β * M⁻¹ ∈ Γ) :
    Z.hom (Additive.ofMul (⟨M * β * M⁻¹, h⟩ : Γ)) = Z.z β (M⁻¹ • q0) := by
  rw [hom_apply, Subgroup.coe_mk, Z.mul_apply, Z.mul_apply, Z.inv_apply]
  have h1 : (M * β)⁻¹ • (q0 : Q) = M⁻¹ • q0 := by
    rw [mul_inv_rev, mul_smul]
    have h' : M * β⁻¹ * M⁻¹ ∈ Γ := by
      have : M * β⁻¹ * M⁻¹ = (M * β * M⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem h
    exact smul_eq_of_conj_mem h'
  rw [h1, smul_inv_smul]
  ring

section Values

def IsAdapted (Z : Cocycle N) (c : Q → ℤ) : Prop :=
  Z.z ModularGroup.S = 0 ∧
    Z.z (ModularGroup.S * ModularGroup.T) = coind (ModularGroup.S * ModularGroup.T) c - c

variable {Z}

theorem T_apply {c : Q → ℤ} (h : Z.IsAdapted c) (p : Q) :
    Z.z ModularGroup.T p = c (ModularGroup.T⁻¹ • p) - c (ModularGroup.S • p) := by
  have hT : Z.z ModularGroup.T p = Z.z (ModularGroup.S⁻¹ * (ModularGroup.S * ModularGroup.T)) p := by
    rw [inv_mul_cancel_left]
  rw [hT, Z.mul_apply, Z.inv_apply, h.1, h.2, inv_inv]
  simp only [Pi.zero_apply, neg_zero, zero_add, Pi.sub_apply, coind_apply]
  rw [← mul_smul, show (ModularGroup.S * ModularGroup.T)⁻¹ * ModularGroup.S = ModularGroup.T⁻¹ by group]

theorem hom_gam_S {c : Q → ℤ} (h : Z.IsAdapted c) (q : Q) :
    Z.hom (Additive.ofMul (gam ModularGroup.S q)) = Z.em (ModularGroup.S • q) - Z.em q := by
  rw [hom_gam, h.1, Pi.zero_apply, zero_add]

theorem hom_gam_T {c : Q → ℤ} (h : Z.IsAdapted c) (q : Q) :
    Z.hom (Additive.ofMul (gam ModularGroup.T q)) =
      c q - c ((ModularGroup.S * ModularGroup.T) • q) + Z.em (ModularGroup.T • q) - Z.em q := by
  rw [hom_gam, T_apply h, inv_smul_smul, ← mul_smul]

theorem T_inv_pow_apply {c : Q → ℤ} (h : Z.IsAdapted c) {n : Q → ℤ}
    (hflux : ∀ q, c (ModularGroup.S • q) - c q = n (ModularGroup.T • q) - n q) (k : ℕ) (p : Q) :
    Z.z (ModularGroup.T⁻¹ ^ k) p =
      (c ((ModularGroup.T ^ k) • p) + n (ModularGroup.T • (ModularGroup.T ^ k) • p)) -
        (c p + n (ModularGroup.T • p)) := by
  induction k generalizing p with
  | zero => simp [Z.one_apply]
  | succ k ih =>
    rw [pow_succ', Z.mul_apply, inv_inv, ih, Z.inv_apply, T_apply h, inv_smul_smul,
      pow_succ, mul_smul]
    linear_combination hflux (ModularGroup.T • p)

theorem T_zpow_apply_eq_zero {c : Q → ℤ} (h : Z.IsAdapted c) {n : Q → ℤ}
    (hflux : ∀ q, c (ModularGroup.S • q) - c q = n (ModularGroup.T • q) - n q) (j : ℤ) (p : Q)
    (hp : (ModularGroup.T ^ j) • p = p) : Z.z (ModularGroup.T ^ j) p = 0 := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · rw [zpow_natCast] at hp ⊢
    have h1 : ModularGroup.T ^ k = (ModularGroup.T⁻¹ ^ k)⁻¹ := by rw [inv_pow, inv_inv]
    have hp' : (ModularGroup.T⁻¹ ^ k) • p = p := by
      rw [inv_pow, inv_smul_eq_iff, hp]
    rw [h1, Z.inv_apply, hp', T_inv_pow_apply h hflux, hp, sub_self, neg_zero]
  · rw [zpow_neg, zpow_natCast, ← inv_pow] at hp ⊢
    have hp' : (ModularGroup.T ^ k) • p = p := by
      rw [inv_pow, inv_smul_eq_iff] at hp; exact hp.symm
    rw [T_inv_pow_apply h hflux, hp', sub_self]

end Values

end Cocycle

theorem exists_conj_apply_one_zero_eq_zero (γ : SL(2, ℤ))
    (h : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    ∃ M : SL(2, ℤ), ((M⁻¹ * γ * M : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
  set a := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  set b := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
  set c := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc
  set d := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd
  have hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := Matrix.eta_fin_two _
  have hdet : a * d - b * c = 1 := by
    have := γ.2; rw [hγ, Matrix.det_fin_two_of] at this; exact this
  have htr : (a + d) ^ 2 = 4 := by
    rw [hγ, Matrix.trace_fin_two_of] at h; exact h
  by_cases hc0 : c = 0
  · exact ⟨1, by simp [← hc, hc0]⟩

  set x : ℚ := (a - d) / (2 * c) with hx
  have hx2 : 2 * (c : ℚ) * x = a - d := by
    rw [hx]; field_simp
  have key : (c : ℚ) * x ^ 2 - (a - d) * x - b = 0 := by
    have hdet' : (a : ℚ) * d - b * c = 1 := by exact_mod_cast hdet
    have htr' : ((a : ℚ) + d) ^ 2 = 4 := by exact_mod_cast htr
    have h4 : 4 * (c : ℚ) * (c * x ^ 2 - (a - d) * x - b) = 0 := by
      linear_combination (2 * c * x - (a - d)) * hx2 - htr' + 4 * hdet'
    have hc' : (4 * c : ℚ) ≠ 0 := by exact_mod_cast (show 4 * c ≠ 0 by omega)
    exact (mul_eq_zero.1 h4).resolve_left hc'
  set p : ℤ := x.num with hp
  set r : ℤ := (x.den : ℤ) with hr
  have hxpr : (p : ℚ) = x * r := by
    rw [hp, hr, Int.cast_natCast, Rat.mul_den_eq_num]
  have hint : c * p ^ 2 - (a - d) * p * r - b * r ^ 2 = 0 := by
    have : ((c * p ^ 2 - (a - d) * p * r - b * r ^ 2 : ℤ) : ℚ) = 0 := by
      push_cast
      rw [hxpr]
      linear_combination (r : ℚ) ^ 2 * key
    exact_mod_cast this
  obtain ⟨u, v, huv⟩ : IsCoprime p r := by
    rw [hp, hr, Int.isCoprime_iff_gcd_eq_one, Int.gcd, Int.natAbs_natCast]
    exact x.reduced
  refine ⟨⟨!![p, -v; r, u], by rw [Matrix.det_fin_two_of]; linear_combination huv⟩, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, hγ]
  simp [Matrix.adjugate_fin_two_of, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination hint

theorem exists_eq_eps_mul_T_zpow (β : SL(2, ℤ)) (h : (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0) :
    ∃ (ε : SL(2, ℤ)) (j : ℤ), (ε = 1 ∨ ε = -1) ∧ β = ε * ModularGroup.T ^ j := by
  have hdet := β.2
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · refine ⟨1, (β : Matrix (Fin 2) (Fin 2) ℤ) 0 1, Or.inl rfl, ?_⟩
    ext i j
    rw [one_mul, ModularGroup.coe_T_zpow]
    fin_cases i <;> fin_cases j <;> simp [h, h0, h1]
  · refine ⟨-1, -(β : Matrix (Fin 2) (Fin 2) ℤ) 0 1, Or.inr rfl, ?_⟩
    ext i j
    rw [neg_one_mul, Matrix.SpecialLinearGroup.coe_neg, ModularGroup.coe_T_zpow]
    fin_cases i <;> fin_cases j <;> simp [h, h0, h1]

theorem isParabolicHom_hom (Z : Cocycle N) {c n : Q → ℤ} (h : Z.IsAdapted c)
    (hflux : ∀ q, c (ModularGroup.S • q) - c q = n (ModularGroup.T • q) - n q) :
    ModularCurve.Period.IsParabolicHom Γ Z.hom := by
  intro γ hγ
  obtain ⟨M, hM⟩ := exists_conj_apply_one_zero_eq_zero (γ : SL(2, ℤ)) hγ
  obtain ⟨ε, j, hε, hβ⟩ := exists_eq_eps_mul_T_zpow _ hM
  have hγeq : (γ : SL(2, ℤ)) = M * (ε * ModularGroup.T ^ j) * M⁻¹ := by rw [← hβ]; group
  have hmem : M * (ε * ModularGroup.T ^ j) * M⁻¹ ∈ Γ := hγeq ▸ γ.2
  have hγ' : γ = ⟨M * (ε * ModularGroup.T ^ j) * M⁻¹, hmem⟩ := Subtype.ext hγeq
  rw [hγ', Z.hom_conj, Z.eps_mul_apply hε]
  apply Cocycle.T_zpow_apply_eq_zero h hflux
  have hmem' : M * ModularGroup.T ^ j * M⁻¹ ∈ Γ := by
    rcases hε with rfl | rfl
    · simpa using hmem
    · have : M * ModularGroup.T ^ j * M⁻¹ = -1 * (M * (-1 * ModularGroup.T ^ j) * M⁻¹) := by
        simp
      rw [this]; exact mul_mem neg_one_mem hmem
  exact smul_eq_of_conj_mem hmem'

open Classical in

def ind (p : Q) (q : Q) : ℤ := if q = p then 1 else 0

theorem sum_ind_mul [Fintype Q] (p : Q) (h : Q → ℂ) : ∑ q, (ind p q : ℂ) * h q = h p := by
  rw [Finset.sum_eq_single p]
  · simp [ind]
  · intro q _ hq; simp [ind, hq]
  · intro hp; exact absurd (Finset.mem_univ p) hp

theorem ind_smul (M : SL(2, ℤ)) (p q : Q) : ind (M • p) q = ind p (M⁻¹ • q) := by
  by_cases hq : q = M • p
  · subst hq; simp [ind]
  · have hq' : M⁻¹ • q ≠ p := fun h' => hq (by rw [← h', smul_inv_smul])
    simp [ind, hq, hq']

variable [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]

def WordProp (M : SL(2, ℤ)) : Prop :=
  ∃ a n : Q → ℤ,
    (∀ q, a (ModularGroup.S • q) - a q + n q - n (ModularGroup.T • q) =
      ind (M⁻¹ • q0) q - ind q0 q) ∧
    ∀ ℓ : SL(2, ℤ) → ℂ, (∀ X, ℓ (X * ModularGroup.T) = ℓ X) → (∀ X, ℓ (-X) = ℓ X) →
      (∀ γ : SL(2, ℤ), γ ∈ Γ → ∀ X,
        ℓ (γ * X * ModularGroup.S) - ℓ (γ * X) = ℓ (X * ModularGroup.S) - ℓ X) →
      ℓ M - ℓ 1 = ∑ q, (a q : ℂ) * (ℓ ((Quotient.out q)⁻¹ * ModularGroup.S) - ℓ (Quotient.out q)⁻¹)

omit [Fintype Q] in
theorem ell_out (ℓ : SL(2, ℤ) → ℂ)
    (hΓ : ∀ γ : SL(2, ℤ), γ ∈ Γ → ∀ X,
      ℓ (γ * X * ModularGroup.S) - ℓ (γ * X) = ℓ (X * ModularGroup.S) - ℓ X) (M : SL(2, ℤ)) :
    ℓ ((Quotient.out (M⁻¹ • (q0 : Q)))⁻¹ * ModularGroup.S) - ℓ (Quotient.out (M⁻¹ • (q0 : Q)))⁻¹ =
      ℓ (M * ModularGroup.S) - ℓ M := by
  rw [smul_q0]
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.Gamma0 N) M⁻¹
  rw [hh, mul_inv_rev, inv_inv]
  exact hΓ _ (inv_mem h.2) M

theorem wordProp_one : WordProp (N := N) 1 := by
  refine ⟨0, 0, fun q => by simp, fun ℓ _ _ _ => by simp⟩

theorem wordProp_mul_T {M : SL(2, ℤ)} (hM : WordProp (N := N) M) :
    WordProp (N := N) (M * ModularGroup.T) := by
  obtain ⟨a, n, h1, h2⟩ := hM
  refine ⟨a, n - ind (M⁻¹ • q0), fun q => ?_, fun ℓ hT hneg hΓ => ?_⟩
  · simp only [Pi.sub_apply]
    rw [mul_inv_rev, mul_smul, ind_smul ModularGroup.T⁻¹ (M⁻¹ • q0) q, inv_inv]
    linear_combination h1 q
  · rw [hT, h2 ℓ hT hneg hΓ]

theorem wordProp_mul_T_inv {M : SL(2, ℤ)} (hM : WordProp (N := N) M) :
    WordProp (N := N) (M * ModularGroup.T⁻¹) := by
  obtain ⟨a, n, h1, h2⟩ := hM
  refine ⟨a, n + ind (ModularGroup.T • M⁻¹ • q0), fun q => ?_, fun ℓ hT hneg hΓ => ?_⟩
  · simp only [Pi.add_apply]
    rw [mul_inv_rev, inv_inv, mul_smul, ind_smul ModularGroup.T (M⁻¹ • q0) (ModularGroup.T • q),
      inv_smul_smul]
    linear_combination h1 q
  · rw [← hT (M * ModularGroup.T⁻¹), inv_mul_cancel_right]
    exact h2 ℓ hT hneg hΓ

theorem wordProp_mul_S {M : SL(2, ℤ)} (hM : WordProp (N := N) M) :
    WordProp (N := N) (M * ModularGroup.S) := by
  obtain ⟨a, n, h1, h2⟩ := hM
  refine ⟨a + ind (M⁻¹ • q0), n, fun q => ?_, fun ℓ hT hneg hΓ => ?_⟩
  · simp only [Pi.add_apply]
    rw [mul_inv_rev, mul_smul, S_inv_smul, ind_smul ModularGroup.S (M⁻¹ • q0) q, S_inv_smul]
    linear_combination h1 q
  · simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib, sum_ind_mul]
    linear_combination h2 ℓ hT hneg hΓ - ell_out ℓ hΓ M

theorem wordProp_mul_S_inv {M : SL(2, ℤ)} (hM : WordProp (N := N) M) :
    WordProp (N := N) (M * ModularGroup.S⁻¹) := by
  obtain ⟨a, n, h1, h2⟩ := wordProp_mul_S hM
  refine ⟨a, n, fun q => ?_, fun ℓ hT hneg hΓ => ?_⟩
  · have e : (M * ModularGroup.S⁻¹)⁻¹ • (q0 : Q) = (M * ModularGroup.S)⁻¹ • q0 := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_smul, mul_smul, S_inv_smul]
    rw [e]; exact h1 q
  · rw [← h2 ℓ hT hneg hΓ, show M * ModularGroup.S⁻¹ = -(M * ModularGroup.S) by
      rw [S_inv, mul_neg], hneg]

theorem wordProp (M : SL(2, ℤ)) : WordProp (N := N) M := by
  have hM : M ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; trivial
  induction hM using Subgroup.closure_induction_right with
  | one => exact wordProp_one
  | mul_right x _ y hy ih =>
    rcases hy with rfl | rfl
    · exact wordProp_mul_S ih
    · exact wordProp_mul_T ih
  | mul_inv_cancel x _ y hy ih =>
    rcases hy with rfl | rfl
    · exact wordProp_mul_S_inv ih
    · exact wordProp_mul_T_inv ih

end Algebra

open UpperHalfPlane Filter Complex MeasureTheory Asymptotics

open scoped Topology ModularForm Real Pointwise

theorem det_entries (γ : SL(2, ℤ)) :
    ((γ 0 0 : ℤ) : ℂ) * γ 1 1 - ((γ 0 1 : ℤ) : ℂ) * γ 1 0 = 1 := by
  have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact_mod_cast this

theorem denom_eq (γ : SL(2, ℤ)) (z : ℂ) :
    denom γ z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  simp [denom]

theorem num_eq (γ : SL(2, ℤ)) (z : ℂ) :
    num γ z = ((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ) := by
  simp [num]

theorem denom_ne_zero' (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : denom γ z ≠ 0 :=
  UpperHalfPlane.denom_ne_zero_of_im γ hz.ne'

def mob (γ : SL(2, ℤ)) (z : ℂ) : ℂ := num γ z / denom γ z

theorem coe_smul (γ : SL(2, ℤ)) (τ : ℍ) : ((γ • τ : ℍ) : ℂ) = mob γ τ := by
  rw [ModularGroup.sl_moeb, coe_smul_of_det_pos (by simp)]; rfl

theorem hasDerivAt_denom (γ : SL(2, ℤ)) (z : ℂ) :
    HasDerivAt (denom (γ : GL (Fin 2) ℝ)) ((γ 1 0 : ℤ) : ℂ) z := by
  have : denom (γ : GL (Fin 2) ℝ) = fun z => ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) :=
    funext (denom_eq γ)
  rw [this]
  simpa using ((hasDerivAt_id z).const_mul ((γ 1 0 : ℤ) : ℂ)).add_const ((γ 1 1 : ℤ) : ℂ)

theorem hasDerivAt_num (γ : SL(2, ℤ)) (z : ℂ) :
    HasDerivAt (num (γ : GL (Fin 2) ℝ)) ((γ 0 0 : ℤ) : ℂ) z := by
  have : num (γ : GL (Fin 2) ℝ) = fun z => ((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ) :=
    funext (num_eq γ)
  rw [this]
  simpa using ((hasDerivAt_id z).const_mul ((γ 0 0 : ℤ) : ℂ)).add_const ((γ 0 1 : ℤ) : ℂ)

theorem hasDerivAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (mob γ) (1 / denom γ z ^ 2) z := by
  have hD := denom_ne_zero' γ hz
  have h := (hasDerivAt_num γ z).div (hasDerivAt_denom γ z) hD
  convert h using 1
  all_goals try rfl
  rw [num_eq, denom_eq, ← det_entries γ]
  simp only [denom_eq] at hD ⊢
  field_simp
  ring

theorem coe_smul_ofComplex (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    ((γ • ofComplex z : ℍ) : ℂ) = mob γ z := by
  rw [coe_smul, ofComplex_apply_of_im_pos hz]

def slashC (φ : ℍ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  φ (σ • ofComplex z) / denom (σ : GL (Fin 2) ℝ) (ofComplex z) ^ 2

theorem slashC_eq_slash (φ : ℍ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) :
    slashC φ σ z = (φ ∣[(2 : ℤ)] σ) (ofComplex z) := by
  rw [slashC, ModularForm.SL_slash_apply, zpow_neg, div_eq_mul_inv]
  norm_cast

section CuspAnalytics

variable {Γ : Subgroup SL(2, ℤ)} (f : CuspForm Γ 2) (σ : SL(2, ℤ))

scoped instance isArithmetic_conj [Γ.FiniteIndex] :
    (ConjAct.toConjAct ((σ : GL (Fin 2) ℝ)⁻¹) •
      ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
  have h := Subgroup.IsArithmetic.conj ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
    (Matrix.SpecialLinearGroup.mapGL ℚ σ)⁻¹
  simp only [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv,
    Matrix.SpecialLinearGroup.map_mapGL] at h
  exact h

def tr : CuspForm (ConjAct.toConjAct ((σ : GL (Fin 2) ℝ)⁻¹) •
    ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) 2 :=
  CuspForm.translate f (σ : GL (Fin 2) ℝ)

theorem coe_tr : ⇑(tr f σ) = (⇑f ∣[(2 : ℤ)] σ) := rfl

theorem slashC_eq_tr : slashC f σ = fun z => tr f σ (ofComplex z) := by
  funext z; rw [slashC_eq_slash, coe_tr]

theorem differentiableOn_slashC : DifferentiableOn ℂ (slashC f σ) {z : ℂ | 0 < z.im} := by
  rw [slashC_eq_tr]
  exact UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo (tr f σ))

theorem continuousOn_slashC : ContinuousOn (slashC f σ) {z : ℂ | 0 < z.im} :=
  (differentiableOn_slashC f σ).continuousOn

variable [Γ.FiniteIndex]

theorem tr_decay {a : ℝ} (ha : 0 < a) :
    ∃ c > 0, ∃ C, 0 ≤ C ∧ ∀ τ : ℍ, a ≤ τ.im → ‖tr f σ τ‖ ≤ C * Real.exp (-c * τ.im) := by
  obtain ⟨c, hc, hO⟩ := CuspFormClass.exp_decay_atImInfty' (tr f σ)
  obtain ⟨C₁, hC₁⟩ := hO.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC₁
  obtain ⟨C₂, hC₂⟩ := CuspFormClass.exists_bound (tr f σ)
  refine ⟨c, hc, max (max C₁ 0) (|C₂| / a * Real.exp (c * max A 0)), ?_, fun τ hτ => ?_⟩
  · exact le_max_of_le_left (le_max_right _ _)
  rcases le_or_gt A τ.im with h | h
  · have := hA τ h
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs, Real.abs_exp] at this
    refine this.trans ?_
    gcongr
    exact le_max_of_le_left (le_max_left _ _)
  · have h2 := hC₂ τ
    have hk : ((2 : ℤ) : ℝ) / 2 = 1 := by norm_num
    rw [hk, Real.rpow_one] at h2
    have hpos := τ.im_pos
    calc ‖tr f σ τ‖ ≤ C₂ / τ.im := h2
      _ ≤ |C₂| / a := by
        rw [div_le_div_iff₀ hpos ha]
        calc C₂ * a ≤ |C₂| * a := by gcongr; exact le_abs_self _
          _ ≤ |C₂| * τ.im := by gcongr
      _ ≤ |C₂| / a * Real.exp (c * max A 0) * Real.exp (-c * τ.im) := by
        rw [mul_assoc, ← Real.exp_add]
        have : 0 ≤ c * max A 0 + -c * τ.im := by
          have : τ.im ≤ max A 0 := h.le.trans (le_max_left _ _)
          nlinarith
        calc |C₂| / a = |C₂| / a * 1 := (mul_one _).symm
          _ ≤ |C₂| / a * Real.exp (c * max A 0 + -c * τ.im) := by
            gcongr; exact Real.one_le_exp this
      _ ≤ _ := by gcongr; exact le_max_right _ _

theorem slashC_decay {a : ℝ} (ha : 0 < a) :
    ∃ c > 0, ∃ C, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.im → ‖slashC f σ z‖ ≤ C * Real.exp (-c * z.im) := by
  obtain ⟨c, hc, C, hC0, hC⟩ := tr_decay f σ ha
  refine ⟨c, hc, C, hC0, fun z hz => ?_⟩
  have hz0 : 0 < z.im := ha.trans_le hz
  have him : (ofComplex z).im = z.im := by rw [ofComplex_apply_of_im_pos hz0]; rfl
  have := hC (ofComplex z) (by rw [him]; exact hz)
  rw [him] at this
  simpa [slashC_eq_tr] using this

end CuspAnalytics

section Primitive

variable {U : ℍ → ℂ} {k : ℍ → ℂ} (σ : SL(2, ℤ))

def V (U : ℍ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) : ℂ := U (σ • ofComplex z)

theorem V_eventuallyEq {z : ℂ} (hz : 0 < z.im) :
    V U σ =ᶠ[𝓝 z] (U ∘ ofComplex) ∘ mob σ := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  simp only [Function.comp_apply, V]
  rw [← coe_smul_ofComplex σ hw, ofComplex_apply]

theorem hasDerivAt_V (hU : ∀ τ : ℍ, HasDerivAt (U ∘ ofComplex) (k τ) τ) {z : ℂ}
    (hz : 0 < z.im) : HasDerivAt (V U σ) (slashC k σ z) z := by
  have h1 : HasDerivAt (U ∘ ofComplex) (k (σ • ofComplex z)) (mob σ z) := by
    have := hU (σ • ofComplex z); rwa [coe_smul_ofComplex σ hz] at this
  have h2 := (h1.comp z (hasDerivAt_mob σ hz)).congr_of_eventuallyEq (V_eventuallyEq σ hz)
  refine h2.congr_deriv ?_
  rw [slashC, mul_one_div, ofComplex_apply_of_im_pos hz]

end Primitive

section Edges

variable {N : ℕ} [NeZero N] (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) {U : ℍ → ℂ}
  (σ : SL(2, ℤ))

theorem sqrt3_div_two_pos : (0 : ℝ) < Real.sqrt 3 / 2 := by positivity

theorem I_mul_integral_ray (hU : ∀ τ : ℍ, HasDerivAt (U ∘ ofComplex) (g τ) τ) {L : ℂ}
    (hL : Tendsto (fun w : ℍ => U (σ • w)) atImInfty (𝓝 L)) :
    Complex.I * ∫ y in Set.Ioi (Real.sqrt 3 / 2), slashC g σ (-(1 / 2) + y * Complex.I) =
      L - V U σ (-(1 / 2) + (Real.sqrt 3 / 2 : ℝ) * Complex.I) := by
  have him : ∀ y : ℝ, (-(1 / 2) + y * Complex.I : ℂ).im = y := fun y => by simp
  have hpath : ∀ y : ℝ, HasDerivAt (fun u : ℂ => (-(1 / 2) + u * Complex.I : ℂ)) Complex.I y :=
    fun y => by simpa using ((hasDerivAt_id (y : ℂ)).mul_const Complex.I).const_add (-(1 / 2) : ℂ)
  have hderiv : ∀ y : ℝ, 0 < y → HasDerivAt (fun y : ℝ => V U σ (-(1 / 2) + y * Complex.I))
      (slashC g σ (-(1 / 2) + y * Complex.I) * Complex.I) y := by
    intro y hy
    have h1 := hasDerivAt_V σ hU (z := -(1 / 2) + y * Complex.I) (by rw [him]; exact hy)
    exact (h1.comp (y : ℂ) (hpath y)).comp_ofReal
  have hcont : ContinuousWithinAt (fun y : ℝ => V U σ (-(1 / 2) + y * Complex.I))
      (Set.Ici (Real.sqrt 3 / 2)) (Real.sqrt 3 / 2) :=
    (hderiv _ sqrt3_div_two_pos).continuousAt.continuousWithinAt

  obtain ⟨c, hc, C, -, hC⟩ := slashC_decay g σ sqrt3_div_two_pos
  have hint : IntegrableOn (fun y : ℝ => slashC g σ (-(1 / 2) + y * Complex.I) * Complex.I)
      (Set.Ioi (Real.sqrt 3 / 2)) := by
    refine Integrable.mul_const ?_ _
    have hpc : Continuous fun y : ℝ => (-(1 / 2) + y * Complex.I : ℂ) := by fun_prop
    have hco : ContinuousOn (fun y : ℝ => slashC g σ (-(1 / 2) + y * Complex.I))
        (Set.Ioi (Real.sqrt 3 / 2)) :=
      (continuousOn_slashC g σ).comp hpc.continuousOn fun y hy => by
        show 0 < (-(1 / 2) + y * Complex.I : ℂ).im
        rw [him]; exact sqrt3_div_two_pos.trans hy
    refine Integrable.mono' ((exp_neg_integrableOn_Ioi _ hc).const_mul C)
      (hco.aestronglyMeasurable measurableSet_Ioi) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
    have := hC (-(1 / 2) + y * Complex.I) (by rw [him]; exact le_of_lt hy)
    simpa using this

  have hlim : Tendsto (fun y : ℝ => V U σ (-(1 / 2) + y * Complex.I)) atTop (𝓝 L) := by
    have hto : Tendsto (fun y : ℝ => ofComplex (-(1 / 2) + y * Complex.I)) atTop atImInfty := by
      rw [atImInfty, tendsto_comap_iff]
      refine tendsto_id.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      simp only [Function.comp_apply, id]
      rw [ofComplex_apply_of_im_pos (by rw [him]; exact hy)]
      exact (him y).symm
    exact hL.comp hto
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun y hy => hderiv y (sqrt3_div_two_pos.trans hy)) hint hlim
  rw [integral_mul_const] at this
  rw [mul_comm, this]

omit [NeZero N] in

theorem integral_arc (hU : ∀ τ : ℍ, HasDerivAt (U ∘ ofComplex) (g τ) τ) :
    ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
        slashC g σ (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I)) =
      V U σ (Complex.exp ((2 * Real.pi / 3 : ℝ) * Complex.I)) -
        V U σ (Complex.exp ((Real.pi / 3 : ℝ) * Complex.I)) := by
  have hmem : ∀ θ ∈ Set.uIcc (Real.pi / 3) (2 * Real.pi / 3),
      0 < (Complex.exp (θ * Complex.I)).im := by
    intro θ hθ
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
    rw [Complex.exp_ofReal_mul_I_im]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos, hθ.1])
      (by linarith [Real.pi_pos, hθ.2])
  have hpath : ∀ θ : ℝ, HasDerivAt (fun u : ℂ => Complex.exp (u * Complex.I))
      (Complex.exp (θ * Complex.I) * Complex.I) θ := fun θ => by
    simpa using ((hasDerivAt_id (θ : ℂ)).mul_const Complex.I).cexp
  have hderiv : ∀ θ ∈ Set.uIcc (Real.pi / 3) (2 * Real.pi / 3),
      HasDerivAt (fun θ : ℝ => V U σ (Complex.exp (θ * Complex.I)))
        (slashC g σ (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I))) θ := by
    intro θ hθ
    have h1 := hasDerivAt_V σ hU (hmem θ hθ)
    have := (h1.comp (θ : ℂ) (hpath θ)).comp_ofReal
    convert this using 1
    all_goals try rfl
    ring
  have hint : IntervalIntegrable (fun θ : ℝ => slashC g σ (Complex.exp (θ * Complex.I)) *
      (Complex.I * Complex.exp (θ * Complex.I))) volume (Real.pi / 3) (2 * Real.pi / 3) := by
    refine ContinuousOn.intervalIntegrable ?_
    have hpc : Continuous fun θ : ℝ => Complex.exp (θ * Complex.I) := by fun_prop
    have h2 : Continuous fun θ : ℝ => Complex.I * Complex.exp (θ * Complex.I) := by fun_prop
    exact ((continuousOn_slashC g σ).comp hpc.continuousOn hmem).mul h2.continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]

end Edges

section Corners

theorem exp_two_pi_div_three :
    Complex.exp ((2 * Real.pi / 3 : ℝ) * Complex.I) = -(1 / 2) + (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
    simp
  · rw [Complex.exp_ofReal_mul_I_im, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_three]
    simp

theorem exp_pi_div_three :
    Complex.exp ((Real.pi / 3 : ℝ) * Complex.I) = (1 / 2) + (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]; simp
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]; simp

def rho : ℍ := ⟨-(1 / 2) + (Real.sqrt 3 / 2 : ℝ) * Complex.I, by simp⟩

def rho' : ℍ := ⟨(1 / 2) + (Real.sqrt 3 / 2 : ℝ) * Complex.I, by simp⟩

@[scoped simp] theorem coe_rho : ((rho : ℍ) : ℂ) = -(1 / 2) + (Real.sqrt 3 / 2 : ℝ) * Complex.I := rfl
@[scoped simp] theorem coe_rho' : ((rho' : ℍ) : ℂ) = (1 / 2) + (Real.sqrt 3 / 2 : ℝ) * Complex.I := rfl

theorem ofComplex_rho : ofComplex (-(1 / 2) + (Real.sqrt 3 / 2 : ℝ) * Complex.I) = rho :=
  ofComplex_apply rho

theorem ofComplex_rho' : ofComplex ((1 / 2) + (Real.sqrt 3 / 2 : ℝ) * Complex.I) = rho' :=
  ofComplex_apply rho'

theorem ofComplex_exp_two_pi_div_three :
    ofComplex (Complex.exp ((2 * Real.pi / 3 : ℝ) * Complex.I)) = rho := by
  rw [exp_two_pi_div_three]; exact ofComplex_rho

theorem ofComplex_exp_pi_div_three :
    ofComplex (Complex.exp ((Real.pi / 3 : ℝ) * Complex.I)) = rho' := by
  rw [exp_pi_div_three]; exact ofComplex_rho'

theorem sqrt3_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem T_smul_rho : ModularGroup.T • rho = rho' := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd, coe_rho, coe_rho']
  push_cast; ring

theorem S_smul_rho' : ModularGroup.S • rho' = rho := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul, coe_rho]
  change (-((rho' : ℍ) : ℂ))⁻¹ = _
  rw [coe_rho', inv_eq_of_mul_eq_one_right]
  have := sqrt3_sq
  push_cast
  linear_combination (-Complex.I ^ 2 / 4) * this + (-3 / 4 : ℂ) * Complex.I_sq

theorem S_smul_rho : ModularGroup.S • rho = rho' := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul, coe_rho']
  change (-((rho : ℍ) : ℂ))⁻¹ = _
  rw [coe_rho, inv_eq_of_mul_eq_one_right]
  have := sqrt3_sq
  push_cast
  linear_combination (-Complex.I ^ 2 / 4) * this + (-3 / 4 : ℂ) * Complex.I_sq

end Corners

section EdgesRead

variable {N : ℕ} [NeZero N] (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) {U : ℍ → ℂ}
  (σ : SL(2, ℤ))

theorem I_mul_integral_ray' (hU : ∀ τ : ℍ, HasDerivAt (U ∘ ofComplex) (g τ) τ) {L : ℂ}
    (hL : Tendsto (fun w : ℍ => U (σ • w)) atImInfty (𝓝 L)) :
    Complex.I * ∫ y in Set.Ioi (Real.sqrt 3 / 2), slashC g σ (-(1 / 2) + y * Complex.I) =
      L - U (σ • rho) := by
  rw [I_mul_integral_ray g σ hU hL, V, ofComplex_rho]

omit [NeZero N] in
theorem integral_arc' (hU : ∀ τ : ℍ, HasDerivAt (U ∘ ofComplex) (g τ) τ) :
    ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
        slashC g σ (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I)) =
      U (σ • rho) - U (σ • rho') := by
  rw [integral_arc g σ hU, V, V, ofComplex_exp_two_pi_div_three, ofComplex_exp_pi_div_three]

end EdgesRead

section Assembly

variable {N : ℕ}

local notation "Γ" => CongruenceSubgroup.Gamma0 N
local notation "Q" => SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N

theorem out_inv_smul (M : SL(2, ℤ)) (q : Q) (τ : ℍ) :
    (Quotient.out (M • q))⁻¹ • τ =
      ((gam M q : Γ) : SL(2, ℤ)) • (Quotient.out q)⁻¹ • M⁻¹ • τ := by
  rw [← mul_smul, ← mul_smul, coe_gam]
  congr 1; group

theorem tendsto_T_zpow_smul (n : ℤ) :
    Tendsto (fun w : ℍ => (ModularGroup.T ^ n) • w) atImInfty atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  have : UpperHalfPlane.im ∘ (fun w : ℍ => (ModularGroup.T ^ n) • w) = UpperHalfPlane.im := by
    funext w
    simp only [Function.comp_apply]
    rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.vadd_im]
  rw [this]
  exact tendsto_comap

section LimitsAtCusps

variable {U : ℍ → ℂ} {L : SL(2, ℤ) → ℂ}
  (hL : ∀ σ : SL(2, ℤ), Tendsto (fun w : ℍ => U (σ • w)) atImInfty (𝓝 (L σ)))
include hL

theorem lim_mul_T (X : SL(2, ℤ)) : L (X * ModularGroup.T) = L X := by
  refine tendsto_nhds_unique (hL _) ?_
  have : (fun w : ℍ => U ((X * ModularGroup.T) • w)) =
      (fun w : ℍ => U (X • w)) ∘ fun w : ℍ => (ModularGroup.T ^ (1 : ℤ)) • w := by
    funext w
    simp [mul_smul]
  rw [this]
  exact (hL X).comp (tendsto_T_zpow_smul 1)

theorem lim_neg (X : SL(2, ℤ)) : L (-X) = L X := by
  refine tendsto_nhds_unique (hL _) ?_
  have : (fun w : ℍ => U ((-X) • w)) = fun w : ℍ => U (X • w) := by
    funext w
    rw [ModularGroup.SL_neg_smul]
  rw [this]
  exact hL X

end LimitsAtCusps

variable [NeZero N] (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) {U : ℍ → ℂ}
  (hU : ModularCurve.HasEquivariantPrimitive N g U)
include hU

theorem U_smul {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    U (γ • τ) = U τ + ModularCurve.period N ⟨γ, hγ⟩ g := by
  have h1 := hU.2.2.1.sub_eq_period ⟨γ, hγ⟩ τ
  have h2 := ModularCurve.period_apply_eq_sub_of_hasEquivariantPrimitive N g hU ⟨γ, hγ⟩
  rw [h2]
  change U (γ • τ) - U τ = U (γ • UpperHalfPlane.I) - U UpperHalfPlane.I at h1
  change U (γ • τ) = U τ + (U (γ • UpperHalfPlane.I) - U UpperHalfPlane.I)
  rw [← h1]; ring

theorem U_smul' (γ : Γ) (τ : ℍ) :
    U ((γ : SL(2, ℤ)) • τ) = U τ + ModularCurve.period N γ g :=
  U_smul g hU γ.2 τ

theorem U_out_inv_smul (M : SL(2, ℤ)) (q : Q) (τ : ℍ) :
    U ((Quotient.out (M • q))⁻¹ • τ) =
      U ((Quotient.out q)⁻¹ • M⁻¹ • τ) + ModularCurve.period N (gam M q) g := by
  rw [out_inv_smul, U_smul' g hU]

theorem lim_coe_mul {L : SL(2, ℤ) → ℂ}
    (hL : ∀ σ : SL(2, ℤ), Tendsto (fun w : ℍ => U (σ • w)) atImInfty (𝓝 (L σ)))
    (γ : Γ) (X : SL(2, ℤ)) :
    L ((γ : SL(2, ℤ)) * X) = L X + ModularCurve.period N γ g := by
  refine tendsto_nhds_unique (hL _) ?_
  have : (fun w : ℍ => U (((γ : SL(2, ℤ)) * X) • w)) =
      fun w : ℍ => U (X • w) + ModularCurve.period N γ g := by
    funext w
    rw [mul_smul, U_smul' g hU]
  rw [this]
  exact (hL X).add_const _

theorem lim_mem_mul {L : SL(2, ℤ) → ℂ}
    (hL : ∀ σ : SL(2, ℤ), Tendsto (fun w : ℍ => U (σ • w)) atImInfty (𝓝 (L σ)))
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (X : SL(2, ℤ)) :
    L (γ * X) = L X + ModularCurve.period N ⟨γ, hγ⟩ g :=
  lim_coe_mul g hU hL ⟨γ, hγ⟩ X

theorem lim_out_smul {L : SL(2, ℤ) → ℂ}
    (hL : ∀ σ : SL(2, ℤ), Tendsto (fun w : ℍ => U (σ • w)) atImInfty (𝓝 (L σ)))
    (M : SL(2, ℤ)) (q : Q) :
    L (Quotient.out (M • q))⁻¹ =
      L ((Quotient.out q)⁻¹ * M⁻¹) + ModularCurve.period N (gam M q) g := by
  refine tendsto_nhds_unique (hL _) ?_
  have : (fun w : ℍ => U ((Quotient.out (M • q))⁻¹ • w)) =
      fun w : ℍ => U (((Quotient.out q)⁻¹ * M⁻¹) • w) + ModularCurve.period N (gam M q) g := by
    funext w
    rw [U_out_inv_smul g hU M q w, mul_smul]
  rw [this]
  exact (hL _).add_const _

end Assembly

end ModularCurve.PoincareDualSurjectivity
p2m_reactivate "P2MW.S_ModularCurve_exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period.ModularCurve P2MW.S_ModularCurve_exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period.ModularCurve.PoincareDualSurjectivity"
p2m_reactivate "P2MW.S_ModularCurve_exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period.ModularCurve P2MW.S_ModularCurve_exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period.ModularCurve.PoincareDualSurjectivity"

open UpperHalfPlane MeasureTheory Filter ModularCurve.PoincareDualSurjectivity

open scoped MatrixGroups Topology

theorem solution
    {N : ℕ} [NeZero N] [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (γT γS : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → CongruenceSubgroup.Gamma0 N)
    (hT : ∀ q, ((γT q : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q)
    (hS : ∀ q, ((γS q : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q)
    (δ : CongruenceSubgroup.Gamma0 N) :
    ∃ φ : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ,
      ModularCurve.Period.IsParabolicHom (CongruenceSubgroup.Gamma0 N) φ ∧
      ∀ (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
        (G : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ → ℂ),
        (∀ q z, G q z = g ((Quotient.out q)⁻¹ • ofComplex z) /
          denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) →
        Complex.I * ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
              ((φ (Additive.ofMul (γT q)) : ℤ) : ℂ) *
                (∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * Complex.I)) +
            1 / 2 * ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
              ((φ (Additive.ofMul (γS q)) : ℤ) : ℂ) *
                (∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
                  G q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I))) =
          ModularCurve.period N δ g := by
  classical
  have hγT : ∀ q, γT q = gam ModularGroup.T q := fun q => Subtype.ext (hT q)
  have hγS : ∀ q, γS q = gam ModularGroup.S q := fun q => Subtype.ext (hS q)

  obtain ⟨a, n, hflux, hword⟩ := wordProp (N := N) (δ : SL(2, ℤ))
  have hδq0 : (δ : SL(2, ℤ))⁻¹ • (q0 : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) = q0 :=
    smul_q0_of_mem (inv_mem δ.2)
  obtain ⟨c, hc⟩ : ∃ c : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℤ, ∀ q, c q = -a q :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℤ, ∀ q, m q = -n q :=
    ⟨_, fun _ => rfl⟩
  have hfl : ∀ q, c (ModularGroup.S • q) - c q = m (ModularGroup.T • q) - m q := fun q => by
    have h := hflux q
    rw [hδq0, sub_self] at h
    rw [hc, hc, hm, hm]
    linear_combination -h

  obtain ⟨Z, hZ⟩ := exists_cocycle (N := N) c
  refine ⟨Z.hom, isParabolicHom_hom Z hZ hfl, fun g G hG => ?_⟩

  obtain ⟨U, hU⟩ := ModularCurve.exists_hasEquivariantPrimitive N g
  choose L hL using hU.2.2.2
  have hGf : ∀ q, G q = slashC g (Quotient.out q)⁻¹ := fun q => funext fun z => hG q z

  obtain ⟨ray, hray⟩ : ∃ ray : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ, ∀ q,
      ray q = ∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * Complex.I) := ⟨_, fun _ => rfl⟩
  obtain ⟨arc, harc⟩ : ∃ arc : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ, ∀ q,
      arc q = ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
        G q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ, ∀ q,
      x q = U ((Quotient.out q)⁻¹ • rho) := ⟨_, fun _ => rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ, ∀ q,
      y q = U ((Quotient.out q)⁻¹ • rho') := ⟨_, fun _ => rfl⟩
  obtain ⟨Lq, hLq⟩ : ∃ Lq : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ, ∀ q,
      Lq q = L (Quotient.out q)⁻¹ := ⟨_, fun _ => rfl⟩
  obtain ⟨LS, hLS⟩ : ∃ LS : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ, ∀ q,
      LS q = L ((Quotient.out q)⁻¹ * ModularGroup.S) := ⟨_, fun _ => rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ cc : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ, ∀ q,
      cc q = ((c q : ℤ) : ℂ) := ⟨_, fun _ => rfl⟩
  obtain ⟨mm, hmm⟩ : ∃ mm : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ, ∀ q,
      mm q = ((Z.em q : ℤ) : ℂ) := ⟨_, fun _ => rfl⟩
  obtain ⟨PTi, hPTi⟩ : ∃ PTi : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ, ∀ q,
      PTi q = ModularCurve.period N (gam ModularGroup.T⁻¹ q) g := ⟨_, fun _ => rfl⟩
  obtain ⟨PS, hPS⟩ : ∃ PS : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ, ∀ q,
      PS q = ModularCurve.period N (gam ModularGroup.S q) g := ⟨_, fun _ => rfl⟩
  obtain ⟨PU, hPU⟩ : ∃ PU : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ, ∀ q,
      PU q = ModularCurve.period N (gam (ModularGroup.S * ModularGroup.T)⁻¹ q) g :=
    ⟨_, fun _ => rfl⟩

  have haT : ∀ q, ((Z.hom (Additive.ofMul (gam ModularGroup.T q)) : ℤ) : ℂ) =
      cc q - cc ((ModularGroup.S * ModularGroup.T) • q) + mm (ModularGroup.T • q) - mm q := by
    intro q
    rw [Cocycle.hom_gam_T hZ, hcc, hcc, hmm, hmm]
    push_cast
    ring
  have haS : ∀ q, ((Z.hom (Additive.ofMul (gam ModularGroup.S q)) : ℤ) : ℂ) =
      mm (ModularGroup.S • q) - mm q := by
    intro q
    rw [Cocycle.hom_gam_S hZ, hmm, hmm]
    push_cast
    ring
  simp only [hγT, hγS, ← hray, ← harc, haT, haS]

  have hrayv : ∀ q, Complex.I * ray q = Lq q - x q := fun q => by
    rw [hray, hGf q, hLq, hx]
    exact I_mul_integral_ray' g _ hU.1 (hL _)
  have harcv : ∀ q, arc q = x q - y q := fun q => by
    rw [harc, hGf q, hx, hy]
    exact integral_arc' g _ hU.1

  have hR1 : ∀ q, Lq (ModularGroup.T⁻¹ • q) = Lq q + PTi q := fun q => by
    rw [hLq, hLq, hPTi, lim_out_smul g hU hL, inv_inv, lim_mul_T hL]
  have hx1 : ∀ q, x (ModularGroup.T⁻¹ • q) = y q + PTi q := fun q => by
    rw [hx, hy, hPTi, U_out_inv_smul g hU, inv_inv, T_smul_rho]
  have hx2 : ∀ q, x (ModularGroup.S • q) = y q + PS q := fun q => by
    rw [hx, hy, hPS, U_out_inv_smul g hU ModularGroup.S q rho,
      inv_smul_eq_iff.mpr S_smul_rho'.symm]
  have hy2 : ∀ q, y (ModularGroup.S • q) = x q + PS q := fun q => by
    rw [hy, hx, hPS, U_out_inv_smul g hU ModularGroup.S q rho',
      inv_smul_eq_iff.mpr S_smul_rho.symm]
  have hR3 : ∀ q, Lq ((ModularGroup.S * ModularGroup.T)⁻¹ • q) = LS q + PU q := fun q => by
    rw [hLq, hLS, hPU, lim_out_smul g hU hL, inv_inv, ← mul_assoc, lim_mul_T hL]
  have hx3 : ∀ q, x ((ModularGroup.S * ModularGroup.T)⁻¹ • q) = x q + PU q := fun q => by
    rw [hx, hx, hPU, U_out_inv_smul g hU, inv_inv, mul_smul, T_smul_rho, S_smul_rho']

  have E1 : Complex.I * ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        (cc q - cc ((ModularGroup.S * ModularGroup.T) • q) + mm (ModularGroup.T • q) - mm q) * ray q =
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, cc q * (Lq q - x q) -
        ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
          cc ((ModularGroup.S * ModularGroup.T) • q) * (Lq q - x q) +
        ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, mm (ModularGroup.T • q) * (Lq q - x q) -
        ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, mm q * (Lq q - x q) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [mul_left_comm, hrayv]
    ring
  have E2a : ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        cc ((ModularGroup.S * ModularGroup.T) • q) * (Lq q - x q) =
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, cc q * (LS q - x q) := by
    rw [← Equiv.sum_comp (MulAction.toPerm (ModularGroup.S * ModularGroup.T)⁻¹)
      (fun q => cc ((ModularGroup.S * ModularGroup.T) • q) * (Lq q - x q))]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [MulAction.toPerm_apply]
    rw [smul_inv_smul, hR3, hx3]
    ring
  have E2b : ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, mm (ModularGroup.T • q) * (Lq q - x q) =
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, mm q * (Lq q - y q) := by
    rw [← Equiv.sum_comp (MulAction.toPerm ModularGroup.T⁻¹)
      (fun q => mm (ModularGroup.T • q) * (Lq q - x q))]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [MulAction.toPerm_apply]
    rw [smul_inv_smul, hR1, hx1]
    ring
  have E3 : ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, (mm (ModularGroup.S • q) - mm q) * arc q =
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, mm (ModularGroup.S • q) * (x q - y q) -
        ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, mm q * (x q - y q) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [harcv]
    ring
  have E3a : ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, mm (ModularGroup.S • q) * (x q - y q) =
      -∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, mm q * (x q - y q) := by
    rw [← Equiv.sum_comp (MulAction.toPerm ModularGroup.S)
      (fun q => mm (ModularGroup.S • q) * (x q - y q)), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [MulAction.toPerm_apply]
    rw [S_smul_S_smul, hx2, hy2]
    ring
  have E5 : ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, cc q * (Lq q - x q) -
        ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, cc q * (LS q - x q) =
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, (a q : ℂ) * (LS q - Lq q) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hcc, hc]
    push_cast
    ring
  have E6 : ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, mm q * (Lq q - y q) -
        ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, mm q * (Lq q - x q) =
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, mm q * (x q - y q) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring

  have hΓ : ∀ γ, γ ∈ CongruenceSubgroup.Gamma0 N → ∀ X : SL(2, ℤ),
      L (γ * X * ModularGroup.S) - L (γ * X) = L (X * ModularGroup.S) - L X := by
    intro γ hγ X
    rw [mul_assoc, lim_mem_mul g hU hL hγ (X * ModularGroup.S), lim_mem_mul g hU hL hγ X]
    ring
  have Wd : L δ - L 1 =
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, (a q : ℂ) * (LS q - Lq q) := by
    rw [hword L (lim_mul_T hL) (lim_neg hL) hΓ]
    exact Finset.sum_congr rfl fun q _ => by rw [hLS, hLq]
  have E7 : ModularCurve.period N δ g = L δ - L 1 := by
    have h := lim_coe_mul g hU hL δ 1
    rw [mul_one] at h
    linear_combination -h
  linear_combination E1 + (1 / 2 : ℂ) * E3 - E2a + E2b + (1 / 2 : ℂ) * E3a + E5 + E6 - Wd - E7

end S_ModularCurve_exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period
end P2MW
export P2MW.S_ModularCurve_exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period (solution)
