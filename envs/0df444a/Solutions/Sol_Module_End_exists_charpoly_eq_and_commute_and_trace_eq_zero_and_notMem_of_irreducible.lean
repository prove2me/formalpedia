-- Prove2me | solution 1 for Module.End.exists_charpoly_eq_and_commute_and_trace_eq_zero_and_notMem_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/387527ff-7365-5008-b89a-f0e7aaffd364

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_exists_charpoly_eq_and_commute_and_trace_eq_zero_and_notMem_of_irreducible

set_option autoImplicit false

open Polynomial Module

universe u v w

noncomputable section

namespace P2mGrp

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

lemma charpoly_eq_of_finrank_eq_two (hV : finrank k V = 2) (T : Module.End k V) :
    T.charpoly = X ^ 2 - C (LinearMap.trace k V T) * X + C (LinearMap.det T) := by
  let b := Module.finBasisOfFinrankEq k V hV
  rw [← LinearMap.charpoly_toMatrix T b, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace k b T, LinearMap.det_toMatrix b T]

lemma charpoly_eq_mul_iff (hV : finrank k V = 2) (T : Module.End k V) (a b : k) :
    T.charpoly = (X - C a) * (X - C b) ↔
      LinearMap.trace k V T = a + b ∧ LinearMap.det T = a * b := by
  have hexp : (X - C a) * (X - C b) = X ^ 2 - C (a + b) * X + C (a * b) := by
    simp only [map_add, map_mul]; ring
  rw [charpoly_eq_of_finrank_eq_two hV, hexp]
  constructor
  · intro h
    have h1 := congrArg (fun q : k[X] => q.coeff 1) h
    have h0 := congrArg (fun q : k[X] => q.coeff 0) h
    simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C] at h1 h0
    norm_num at h1 h0
    exact ⟨by linear_combination -h1, h0⟩
  · rintro ⟨h1, h0⟩
    rw [h1, h0]

lemma mul_self_eq_smul_one_of_trace_eq_zero (hV : finrank k V = 2) (m : Module.End k V)
    (hm : LinearMap.trace k V m = 0) : m * m = (-LinearMap.det m) • (1 : Module.End k V) := by
  have h := LinearMap.aeval_self_charpoly m
  rw [charpoly_eq_of_finrank_eq_two hV, hm] at h
  simp only [map_zero, zero_mul, sub_zero, map_add, aeval_X_pow, aeval_C,
    Module.algebraMap_end_eq_smul_id] at h
  rw [pow_two] at h
  rw [neg_smul, eq_neg_iff_add_eq_zero]
  exact h

lemma sub_smul_one_mul_self_eq_zero (hV : finrank k V = 2) {T : Module.End k V} {μ : k}
    (h : T.charpoly = (X - C μ) * (X - C μ)) :
    (T - μ • 1) * (T - μ • 1) = 0 := by
  have h' := LinearMap.aeval_self_charpoly T
  rw [h] at h'
  simp [Module.algebraMap_end_eq_smul_id] at h'
  exact h'

lemma smul_one_injective (hV : finrank k V = 2) {a b : k}
    (h : a • (1 : Module.End k V) = b • 1) : a = b := by
  have hne : (1 : Module.End k V) ≠ 0 := by
    intro h1
    haveI : Subsingleton V := ⟨fun v w => by
      have hv := LinearMap.congr_fun h1 v
      have hw := LinearMap.congr_fun h1 w
      simp only [Module.End.one_apply, LinearMap.zero_apply] at hv hw
      rw [hv, hw]⟩
    have : finrank k V = 0 := Module.finrank_zero_of_subsingleton
    omega
  exact smul_left_injective k hne h

lemma det_ne_zero {H : Type w} [Group H] (ρ : H →* Module.End k V) (h : H) :
    LinearMap.det (ρ h) ≠ 0 :=
  (((Group.isUnit h).map ρ).map LinearMap.det).ne_zero

lemma rho_mul_inv {H : Type w} [Group H] (ρ : H →* Module.End k V) (g : H) :
    ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]

lemma rho_inv_mul {H : Type w} [Group H] (ρ : H →* Module.End k V) (g : H) :
    ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]

lemma exists_basis_of_mul_self_eq_zero (hV : finrank k V = 2) {n : Module.End k V}
    (hn : n ≠ 0) (hsq : n * n = 0) :
    ∃ b : Basis (Fin 2) k V, n (b 0) = 0 ∧ n (b 1) = b 0 := by
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : V, n e₂ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hn (LinearMap.ext hall)
  set e₁ := n e₂ with he₁
  have hne₁ : n e₁ = 0 := by
    rw [he₁, ← Module.End.mul_apply, hsq, LinearMap.zero_apply]
  have hli : LinearIndependent k ![e₁, e₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg n hst
    rw [map_add, map_smul, map_smul, hne₁, smul_zero, zero_add, map_zero, ← he₁] at h1
    have ht : t = 0 := (smul_eq_zero.1 h1).resolve_right he₂
    rw [ht, zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.1 hst).resolve_right he₂, ht⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [hV]), ?_, ?_⟩
  · rw [coe_basisOfLinearIndependentOfCardEqFinrank]; exact hne₁
  · rw [coe_basisOfLinearIndependentOfCardEqFinrank]; rfl

lemma toMatrix_eq_of_adapted {n : Module.End k V} {b : Basis (Fin 2) k V}
    (h0 : n (b 0) = 0) (h1 : n (b 1) = b 0) :
    LinearMap.toMatrix b b n = !![0, 1; 0, 0] := by
  have : n = Matrix.toLin b b !![0, 1; 0, 0] := by
    apply b.ext
    intro j
    fin_cases j
    · simp [Matrix.toLin_self, Fin.sum_univ_two, h0]
    · simp [Matrix.toLin_self, Fin.sum_univ_two, h1]
  rw [this, LinearMap.toMatrix_toLin]

lemma mul_self_eq_zero_of_commute_nilpotent (h2 : (2 : k) ≠ 0) (hV : finrank k V = 2)
    {n m : Module.End k V} (hn : n ≠ 0) (hsq : n * n = 0) (hcomm : m * n = n * m)
    (hm : LinearMap.trace k V m = 0) : m * m = 0 := by
  classical
  obtain ⟨b, hb0, hb1⟩ := exists_basis_of_mul_self_eq_zero hV hn hsq
  have hN := toMatrix_eq_of_adapted hb0 hb1
  set M := LinearMap.toMatrix b b m with hM
  have hc := congrArg (LinearMap.toMatrix b b) hcomm
  rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, hN, ← hM] at hc
  have h10 : M 1 0 = 0 := by
    have := congrFun (congrFun hc 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this.symm
  have hdiag : M 0 0 = M 1 1 := by
    have := congrFun (congrFun hc 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have htr : M 0 0 + M 1 1 = 0 := by
    rw [hM, ← Matrix.trace_fin_two, ← LinearMap.trace_eq_matrix_trace k b m, hm]
  have h00 : M 0 0 = 0 := by
    have : (2 : k) * M 0 0 = 0 := by linear_combination htr + hdiag
    exact (mul_eq_zero.1 this).resolve_left h2
  have h11 : M 1 1 = 0 := by rw [← hdiag, h00]
  apply (LinearMap.toMatrix b b).injective
  rw [LinearMap.toMatrix_mul, ← hM, map_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h10, h11]

section Reg

variable {H : Type w} [Group H] (ρ : H →* Module.End k V)

def IsReg (h : H) : Prop := ∃ α β : k, α ≠ β ∧ (ρ h).charpoly = (X - C α) * (X - C β)

variable {ρ}

lemma isReg_iff (hV : finrank k V = 2) (h : H) :
    IsReg ρ h ↔ ∃ α β : k, α ≠ β ∧ LinearMap.trace k V (ρ h) = α + β ∧
      LinearMap.det (ρ h) = α * β := by
  simp only [IsReg, charpoly_eq_mul_iff hV]

lemma IsReg.conj (hV : finrank k V = 2) {h : H} (hh : IsReg ρ h) (g : H) :
    IsReg ρ (g * h * g⁻¹) := by
  rw [isReg_iff hV] at hh ⊢
  obtain ⟨α, β, hαβ, htr, hdet⟩ := hh
  have hρ : ρ (g * h * g⁻¹) = ρ g * ρ h * ρ g⁻¹ := by rw [map_mul ρ, map_mul ρ]
  refine ⟨α, β, hαβ, ?_, ?_⟩
  · rw [hρ, LinearMap.trace_mul_comm, ← mul_assoc, rho_inv_mul, one_mul, htr]
  · rw [hρ, map_mul LinearMap.det, map_mul LinearMap.det, mul_comm, ← mul_assoc,
      ← map_mul LinearMap.det, rho_inv_mul, map_one, one_mul, hdet]

lemma isReg_of_trace_eq_zero (h2 : (2 : k) ≠ 0) (hV : finrank k V = 2)
    (hsplit : ∀ h : H, ∃ α β : k, (ρ h).charpoly = (X - C α) * (X - C β))
    {g : H} (hg : LinearMap.trace k V (ρ g) = 0) : IsReg ρ g := by
  obtain ⟨α, β, hαβ⟩ := hsplit g
  refine ⟨α, β, ?_, hαβ⟩
  rw [charpoly_eq_mul_iff hV] at hαβ
  rintro rfl
  have hα : α = 0 := by
    have : (2 : k) * α = 0 := by linear_combination hαβ.1.symm.trans hg
    exact (mul_eq_zero.1 this).resolve_left h2
  apply det_ne_zero ρ g
  rw [hαβ.2, hα, mul_zero]

lemma exists_charpoly_eq_sq_of_not_isReg
    (hsplit : ∀ h : H, ∃ α β : k, (ρ h).charpoly = (X - C α) * (X - C β))
    {h : H} (hh : ¬ IsReg ρ h) : ∃ μ : k, (ρ h).charpoly = (X - C μ) * (X - C μ) := by
  obtain ⟨α, β, hαβ⟩ := hsplit h
  by_cases hne : α = β
  · exact ⟨α, by rw [hαβ, hne]⟩
  · exact absurd ⟨α, β, hne, hαβ⟩ hh

lemma exists_isReg (h2 : (2 : k) ≠ 0) (hV : finrank k V = 2)
    (hirr : ∀ W : Submodule k V, (∀ h : H, ∀ x ∈ W, ρ h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hsplit : ∀ h : H, ∃ α β : k, (ρ h).charpoly = (X - C α) * (X - C β)) :
    ∃ h : H, IsReg ρ h := by
  classical
  by_contra hnone
  push Not at hnone
  have hsq : ∀ h : H, ∃ μ : k, (ρ h).charpoly = (X - C μ) * (X - C μ) :=
    fun h => exists_charpoly_eq_sq_of_not_isReg hsplit (hnone h)
  have hdisc : ∀ h : H, (LinearMap.trace k V (ρ h)) ^ 2 = 4 * LinearMap.det (ρ h) := by
    intro h
    obtain ⟨μ, hμ⟩ := hsq h
    rw [charpoly_eq_mul_iff hV] at hμ
    rw [hμ.1, hμ.2]; ring

  have hline : ∀ v : V, v ≠ 0 → (k ∙ v) ≠ ⊥ ∧ (k ∙ v) ≠ ⊤ := by
    intro v hv
    refine ⟨?_, ?_⟩
    · rw [Ne, Submodule.span_singleton_eq_bot]; exact hv
    · intro htop
      have := finrank_span_singleton (K := k) hv
      rw [htop, finrank_top, hV] at this
      omega
  by_cases hscalar : ∀ h : H, ∃ μ : k, ρ h = μ • 1
  ·
    obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
      have : 0 < finrank k V := by omega
      exact Module.finrank_pos_iff_exists_ne_zero.1 this
    have hst : ∀ h : H, ∀ x ∈ k ∙ v, ρ h x ∈ k ∙ v := by
      intro h x hx
      obtain ⟨μ, hμ⟩ := hscalar h
      rw [hμ]
      exact Submodule.smul_mem _ μ (by simpa using hx)
    rcases hirr _ hst with h | h
    · exact (hline v hv).1 h
    · exact (hline v hv).2 h
  push Not at hscalar
  obtain ⟨h₁, hh₁⟩ := hscalar
  obtain ⟨μ₁, hμ₁⟩ := hsq h₁
  set n₁ : Module.End k V := ρ h₁ - μ₁ • 1 with hn₁def
  have hn₁sq : n₁ * n₁ = 0 := sub_smul_one_mul_self_eq_zero hV hμ₁
  have hn₁ : n₁ ≠ 0 := fun h => hh₁ μ₁ (sub_eq_zero.1 h)
  obtain ⟨b, hb0, hb1⟩ := exists_basis_of_mul_self_eq_zero hV hn₁ hn₁sq

  have hμ₁ : μ₁ ≠ 0 := by
    intro h0
    apply det_ne_zero ρ h₁
    rw [charpoly_eq_mul_iff hV] at hμ₁
    rw [hμ₁.2, h0, mul_zero]

  have hN₁ : LinearMap.toMatrix b b (ρ h₁) = !![μ₁, 1; 0, μ₁] := by
    have h0' : ρ h₁ (b 0) = μ₁ • b 0 := by
      have := hb0
      rw [hn₁def, LinearMap.sub_apply, sub_eq_zero] at this
      simpa using this
    have h1' : ρ h₁ (b 1) = μ₁ • b 1 + b 0 := by
      have := hb1
      rw [hn₁def, LinearMap.sub_apply, sub_eq_iff_eq_add] at this
      rw [this]; simp [add_comm]
    have : ρ h₁ = Matrix.toLin b b !![μ₁, 1; 0, μ₁] := by
      apply b.ext
      intro j
      fin_cases j
      · simp [Matrix.toLin_self, Fin.sum_univ_two, h0']
      · simp [Matrix.toLin_self, Fin.sum_univ_two, h1', add_comm]
    rw [this, LinearMap.toMatrix_toLin]

  have hdiscM : ∀ h : H, (Matrix.trace (LinearMap.toMatrix b b (ρ h))) ^ 2 =
      4 * (LinearMap.toMatrix b b (ρ h)).det := by
    intro h
    rw [← LinearMap.trace_eq_matrix_trace k b, LinearMap.det_toMatrix]
    exact hdisc h

  have hupper : ∀ h : H, LinearMap.toMatrix b b (ρ h) 1 0 = 0 := by
    intro h
    set A := LinearMap.toMatrix b b (ρ h) with hA
    have d0 := hdiscM h
    have d1 := hdiscM (h * h₁)
    have d2 := hdiscM (h * h₁ * h₁)
    rw [map_mul ρ, LinearMap.toMatrix_mul, ← hA, hN₁] at d1
    rw [map_mul ρ, map_mul ρ, LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, ← hA, hN₁] at d2
    rw [← hA] at d0
    simp only [Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at d0 d1 d2
    have e1 : A 1 0 * (2 * μ₁ * (A 0 0 + A 1 1) + A 1 0) = 0 := by
      linear_combination d1 - μ₁ ^ 2 * d0
    have e2 : (4 * μ₁ ^ 2) * (A 1 0 * (μ₁ * (A 0 0 + A 1 1) + A 1 0)) = 0 := by
      linear_combination d2 - μ₁ ^ 4 * d0
    have h4 : (4 : k) * μ₁ ^ 2 ≠ 0 := by
      refine mul_ne_zero ?_ (pow_ne_zero 2 hμ₁)
      have : (4 : k) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    have e2' := (mul_eq_zero.1 e2).resolve_left h4
    by_contra hc
    have f1 := (mul_eq_zero.1 e1).resolve_left hc
    have f2 := (mul_eq_zero.1 e2').resolve_left hc
    apply hc
    linear_combination 2 * f2 - f1

  have hst : ∀ h : H, ∀ x ∈ k ∙ b 0, ρ h x ∈ k ∙ b 0 := by
    intro h x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul]
    apply Submodule.smul_mem
    have : ρ h (b 0) = ∑ i, LinearMap.toMatrix b b (ρ h) i 0 • b i := by
      conv_lhs => rw [← Matrix.toLin_toMatrix b b (ρ h)]
      rw [Matrix.toLin_self]
    rw [this, Fin.sum_univ_two, hupper h, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  rcases hirr _ hst with h | h
  · exact (hline _ (b.ne_zero 0)).1 h
  · exact (hline _ (b.ne_zero 0)).2 h

lemma false_of_forall_commute (hV : finrank k V = 2)
    (hirr : ∀ W : Submodule k V, (∀ h : H, ∀ x ∈ W, ρ h x ∈ W) → W = ⊥ ∨ W = ⊤)
    {h₀ : H} (hreg : IsReg ρ h₀) (hcomm : ∀ g : H, ρ g * ρ h₀ = ρ h₀ * ρ g) : False := by
  obtain ⟨α, β, hαβ, hchar⟩ := hreg
  have hroot : (ρ h₀).charpoly.IsRoot α := by
    rw [hchar]; simp
  have heig : (ρ h₀).HasEigenvalue α :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 hroot
  let W : Submodule k V := (ρ h₀).eigenspace α
  have hst : ∀ g : H, ∀ x ∈ W, ρ g x ∈ W := by
    intro g x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [← Module.End.mul_apply, ← hcomm, Module.End.mul_apply, hx, map_smul]
  rcases hirr W hst with h | h
  · exact (Module.End.hasEigenvalue_iff.1 heig) h
  ·
    have hall : ∀ v : V, ρ h₀ v = α • v := fun v =>
      Module.End.mem_eigenspace_iff.1 (h ▸ Submodule.mem_top : v ∈ W)
    have htr : LinearMap.trace k V (ρ h₀) = 2 * α := by
      have : ρ h₀ = α • 1 := LinearMap.ext fun v => by simpa using hall v
      rw [this, map_smul, LinearMap.trace_one, hV]; simp [mul_comm]
    rw [charpoly_eq_mul_iff hV] at hchar
    apply hαβ
    linear_combination -(hchar.1.symm.trans htr)

end Reg

section Pairing

variable (k V)

def tracePairing :
    LinearMap.ker (LinearMap.trace k V) →ₗ[k] Module.Dual k (LinearMap.ker (LinearMap.trace k V)) :=
  LinearMap.mk₂ k
    (fun Y X => LinearMap.trace k V ((Y : Module.End k V) * (X : Module.End k V)))
    (fun Y₁ Y₂ X => by simp [add_mul])
    (fun c Y X => by simp)
    (fun Y X₁ X₂ => by simp [mul_add])
    (fun c Y X => by simp)

@[scoped simp]
theorem tracePairing_apply (Y X : LinearMap.ker (LinearMap.trace k V)) :
    tracePairing k V Y X = LinearMap.trace k V ((Y : Module.End k V) * (X : Module.End k V)) :=
  rfl

variable {k V}

theorem tracePairing_injective (h2 : (2 : k) ≠ 0) (hV : finrank k V = 2) :
    Function.Injective (tracePairing k V) := by
  classical
  let b : Basis (Fin 2) k V := Module.finBasisOfFinrankEq k V hV
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro Y hY
  rw [LinearMap.mem_ker] at hY
  have htest : ∀ E : Matrix (Fin 2) (Fin 2) k, E.trace = 0 →
      (LinearMap.toMatrix b b (Y : Module.End k V) * E).trace = 0 := by
    intro E hE
    have hX : Matrix.toLin b b E ∈ LinearMap.ker (LinearMap.trace k V) := by
      rw [LinearMap.mem_ker, LinearMap.trace_eq_matrix_trace k b, LinearMap.toMatrix_toLin, hE]
    have h0 : tracePairing k V Y ⟨Matrix.toLin b b E, hX⟩ = 0 := by
      rw [hY]; rfl
    rw [tracePairing_apply, LinearMap.trace_eq_matrix_trace k b, LinearMap.toMatrix_mul,
      LinearMap.toMatrix_toLin] at h0
    exact h0
  set A := LinearMap.toMatrix b b (Y : Module.End k V) with hA
  have htrA : A 0 0 + A 1 1 = 0 := by
    have := Y.2
    rw [LinearMap.mem_ker, LinearMap.trace_eq_matrix_trace k b, Matrix.trace_fin_two] at this
    exact this
  have h01 := htest !![0, 1; 0, 0] (by simp [Matrix.trace_fin_two])
  have h10 := htest !![0, 0; 1, 0] (by simp [Matrix.trace_fin_two])
  have hdiag := htest !![1, 0; 0, -1] (by simp [Matrix.trace_fin_two])
  rw [Matrix.trace_fin_two] at h01 h10 hdiag
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01 h10 hdiag
  have h00 : A 0 0 = 0 := by
    have : (2 : k) * A 0 0 = 0 := by linear_combination htrA + hdiag
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h2
    · exact h
  have h11 : A 1 1 = 0 := by linear_combination htrA - h00
  have hA0 : A = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  apply Subtype.ext
  change (Y : Module.End k V) = 0
  apply (LinearMap.toMatrix b b).injective
  rw [← hA, hA0, map_zero]

theorem tracePairing_surjective (h2 : (2 : k) ≠ 0) (hV : finrank k V = 2) :
    Function.Surjective (tracePairing k V) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := k) (V := LinearMap.ker (LinearMap.trace k V))).symm).mp
    (tracePairing_injective h2 hV)

lemma finrank_ker_trace (h2 : (2 : k) ≠ 0) (hV : finrank k V = 2) :
    finrank k (LinearMap.ker (LinearMap.trace k V)) = 3 := by
  have hE : finrank k (Module.End k V) = 4 := by
    rw [Module.finrank_linearMap, hV]
  have hsurj : LinearMap.range (LinearMap.trace k V) = ⊤ := by
    rw [eq_top_iff]
    rintro a -
    refine ⟨(a / 2) • (1 : Module.End k V), ?_⟩
    rw [map_smul, LinearMap.trace_one, hV, smul_eq_mul]
    push_cast
    field_simp
  have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.trace k V)
  rw [hsurj, finrank_top, Module.finrank_self, hE] at h
  omega

end Pairing

section Main

variable {H : Type w} [Group H] {ρ : H →* Module.End k V}

def conjS (ρ : H →* Module.End k V) (g : H) :
    LinearMap.ker (LinearMap.trace k V) →ₗ[k] LinearMap.ker (LinearMap.trace k V) :=
  ((LinearMap.mulLeft k (ρ g)) ∘ₗ (LinearMap.mulRight k (ρ g⁻¹))).restrict
    (p := LinearMap.ker (LinearMap.trace k V)) (q := LinearMap.ker (LinearMap.trace k V))
    (fun x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
        LinearMap.mulLeft_apply]
      rw [LinearMap.trace_mul_comm, mul_assoc, rho_inv_mul, mul_one, hx])

lemma coe_conjS (g : H) (x : LinearMap.ker (LinearMap.trace k V)) :
    ((conjS ρ g x : LinearMap.ker (LinearMap.trace k V)) : Module.End k V) =
      ρ g * (x : Module.End k V) * ρ g⁻¹ := by
  change ρ g * ((x : Module.End k V) * ρ g⁻¹) = _
  rw [mul_assoc]

lemma conjS_inv_conjS (g : H) (x : LinearMap.ker (LinearMap.trace k V)) :
    conjS ρ g⁻¹ (conjS ρ g x) = x := by
  apply Subtype.ext
  simp only [coe_conjS, inv_inv]
  rw [← mul_assoc, ← mul_assoc, rho_inv_mul, one_mul, mul_assoc, rho_inv_mul, mul_one]

set_option maxHeartbeats 6400000 in
theorem main (h2 : (2 : k) ≠ 0) (hV : finrank k V = 2)
    (hirr : ∀ W : Submodule k V, (∀ h : H, ∀ x ∈ W, ρ h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hsplit : ∀ h : H, ∃ α β : k, (ρ h).charpoly = (X - C α) * (X - C β))
    (U : AddSubgroup (Module.End k V))
    (hU : ∀ h : H, ∀ m ∈ U, ρ h * m * ρ h⁻¹ ∈ U)
    (hproper : ∃ m : Module.End k V, LinearMap.trace k V m = 0 ∧ m ∉ U) :
    ∃ h : H, ∃ α β : k, α ≠ β ∧ (ρ h).charpoly = (X - C α) * (X - C β) ∧
      ∃ m : Module.End k V, LinearMap.trace k V m = 0 ∧ m * ρ h = ρ h * m ∧ m ∉ U := by
  classical
  by_contra H0
  push Not at H0

  have H0' : ∀ h : H, IsReg ρ h → ∀ m : Module.End k V, LinearMap.trace k V m = 0 →
      m * ρ h = ρ h * m → m ∈ U := by
    rintro h ⟨α, β, hαβ, hchar⟩ m hm hcomm
    exact H0 h α β hαβ hchar m hm hcomm

  set S : Submodule k (Module.End k V) := LinearMap.ker (LinearMap.trace k V) with hSdef
  have memS : ∀ m : Module.End k V, m ∈ S ↔ LinearMap.trace k V m = 0 := fun m => LinearMap.mem_ker
  have hS3 : finrank k S = 3 := finrank_ker_trace h2 hV

  let Uset : Set S := {x | ∃ h : H, IsReg ρ h ∧ (x : Module.End k V) * ρ h = ρ h * x}
  let U' : Submodule k S := Submodule.span k Uset

  have hU'U : ∀ x ∈ U', (x : Module.End k V) ∈ U := by
    intro x hx
    suffices h : ∀ a : k, ((a • x : S) : Module.End k V) ∈ U by simpa using h 1
    induction hx using Submodule.span_induction with
    | mem x hx =>
      intro a
      obtain ⟨h, hh, hcomm⟩ := hx
      refine H0' h hh _ (by rw [Submodule.coe_smul, map_smul, (memS _).1 x.2, smul_zero]) ?_
      rw [Submodule.coe_smul, smul_mul_assoc, hcomm, mul_smul_comm]
    | zero => intro a; simp [U.zero_mem]
    | add x y _ _ hx hy => intro a; simpa [smul_add] using U.add_mem (hx a) (hy a)
    | smul a x _ hx => intro b; simpa [smul_smul] using hx (b * a)

  have hUsetconj : ∀ g : H, ∀ x ∈ Uset, conjS ρ g x ∈ Uset := by
    rintro g x ⟨h, hh, hcomm⟩
    refine ⟨g * h * g⁻¹, hh.conj hV g, ?_⟩
    rw [coe_conjS, map_mul, map_mul]
    calc ρ g * (x : Module.End k V) * ρ g⁻¹ * (ρ g * ρ h * ρ g⁻¹)
        = ρ g * (x : Module.End k V) * (ρ g⁻¹ * ρ g) * ρ h * ρ g⁻¹ := by simp only [mul_assoc]
      _ = ρ g * ((x : Module.End k V) * ρ h) * ρ g⁻¹ := by rw [rho_inv_mul, mul_one, mul_assoc (ρ g)]
      _ = ρ g * (ρ h * (x : Module.End k V)) * ρ g⁻¹ := by rw [hcomm]
      _ = ρ g * ρ h * (ρ g⁻¹ * ρ g) * (x : Module.End k V) * ρ g⁻¹ := by
          rw [rho_inv_mul, mul_one]; simp only [mul_assoc]
      _ = ρ g * ρ h * ρ g⁻¹ * (ρ g * (x : Module.End k V) * ρ g⁻¹) := by simp only [mul_assoc]
  have hU'conj : ∀ g : H, ∀ x ∈ U', conjS ρ g x ∈ U' := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hUsetconj g x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact U'.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact U'.smul_mem a hx

  obtain ⟨m₀, hm₀, hm₀U⟩ := hproper
  have hm₀U' : (⟨m₀, (memS _).2 hm₀⟩ : S) ∉ U' := fun h => hm₀U (hU'U _ h)
  have hU'lt : U' < ⊤ := lt_top_iff_ne_top.2 fun h => hm₀U' (h ▸ Submodule.mem_top)
  have hU'le2 : finrank k U' ≤ 2 := by
    have := Submodule.finrank_lt_finrank_of_lt hU'lt
    rw [finrank_top, hS3] at this
    omega

  obtain ⟨h₀, hh₀⟩ := exists_isReg h2 hV hirr hsplit
  obtain ⟨α₀, β₀, hαβ₀, hchar₀⟩ := hh₀
  have htd₀ := (charpoly_eq_mul_iff hV _ _ _).1 hchar₀
  set z₀E : Module.End k V := ρ h₀ - ((α₀ + β₀) / 2) • 1 with hz₀E
  have hz₀tr : LinearMap.trace k V z₀E = 0 := by
    rw [hz₀E, map_sub, map_smul, LinearMap.trace_one, hV, htd₀.1, smul_eq_mul]
    push_cast; field_simp; ring
  set z₀ : S := ⟨z₀E, (memS _).2 hz₀tr⟩ with hz₀
  have hz₀comm : z₀E * ρ h₀ = ρ h₀ * z₀E := by
    rw [hz₀E, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hz₀mem : z₀ ∈ Uset := ⟨h₀, ⟨α₀, β₀, hαβ₀, hchar₀⟩, hz₀comm⟩
  have hz₀U' : z₀ ∈ U' := Submodule.subset_span hz₀mem
  have hz₀ne : z₀ ≠ 0 := by
    intro h
    have h' : z₀E = 0 := congrArg Subtype.val h
    rw [hz₀E, sub_eq_zero] at h'
    apply hαβ₀
    have hdet := congrArg LinearMap.det h'
    rw [LinearMap.det_smul, map_one, mul_one, hV, htd₀.2] at hdet

    have e : (α₀ + β₀) / 2 * 2 = α₀ + β₀ := div_mul_cancel₀ _ h2
    have : (α₀ - β₀) ^ 2 = 0 := by
      linear_combination (-(α₀ + β₀ + (α₀ + β₀) / 2 * 2)) * e - 4 * hdet
    exact sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
  have hU'pos : 1 ≤ finrank k U' := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro h
    exact hz₀ne ((Submodule.eq_bot_iff _).1 h z₀ hz₀U')

  have hkey : ∃ m : S, m ≠ 0 ∧ (∀ g : H, ∃ χ : k, conjS ρ g m = χ • m) ∧
      ((m = z₀ ∧ ∀ y ∈ U', ∃ c : k, y = c • m) ∨
        (∀ u ∈ U', LinearMap.trace k V ((u : Module.End k V) * m) = 0)) := by
    rcases Nat.lt_or_ge (finrank k U') 2 with hlt | hge
    ·
      have h1 : finrank k U' = 1 := by omega
      have hline : ∀ y ∈ U', ∃ c : k, y = c • z₀ := by
        intro y hy
        have := (finrank_eq_one_iff_of_nonzero' (⟨z₀, hz₀U'⟩ : U')
          (fun h => hz₀ne (congrArg Subtype.val h))).1 h1 ⟨y, hy⟩
        obtain ⟨c, hc⟩ := this
        have hc' := congrArg Subtype.val hc
        rw [Submodule.coe_smul] at hc'
        exact ⟨c, hc'.symm⟩
      refine ⟨z₀, hz₀ne, fun g => ?_, Or.inl ⟨rfl, hline⟩⟩
      obtain ⟨c, hc⟩ := hline _ (hU'conj g z₀ hz₀U')
      exact ⟨c, hc⟩
    ·
      have h2' : finrank k U' = 2 := le_antisymm hU'le2 hge
      obtain ⟨L, hL⟩ : ∃ L : Submodule k S,
          L = LinearMap.BilinForm.orthogonal (tracePairing k V) U' := ⟨_, rfl⟩
      have hLdim : finrank k L = 1 := by
        have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := tracePairing k V) U'
        rw [LinearMap.ker_eq_bot.2 (tracePairing_injective h2 hV), inf_bot_eq, finrank_bot,
          add_zero, h2', hS3, ← hL] at h
        exact Nat.add_left_cancel (h.trans (by norm_num : (3 : ℕ) = 2 + 1))
      have memL : ∀ x : S, x ∈ L ↔
          ∀ u ∈ U', LinearMap.trace k V ((u : Module.End k V) * x) = 0 := fun x => by
        rw [hL]; exact Iff.rfl
      have hLne : L ≠ ⊥ := fun h => by
        rw [h, finrank_bot] at hLdim
        exact zero_ne_one hLdim
      obtain ⟨m, hmL, hmne⟩ := (Submodule.ne_bot_iff L).1 hLne
      have hLline : ∀ y ∈ L, ∃ c : k, y = c • m := by
        intro y hy
        obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨m, hmL⟩ : L)
          (fun h => hmne (congrArg Subtype.val h))).1 hLdim ⟨y, hy⟩
        have hc' := congrArg Subtype.val hc
        rw [Submodule.coe_smul] at hc'
        exact ⟨c, hc'.symm⟩

      have hLconj : ∀ g : H, conjS ρ g m ∈ L := by
        intro g
        rw [memL]
        intro u hu
        have hu' := (memL m).1 hmL _ (hU'conj g⁻¹ u hu)
        rw [coe_conjS, inv_inv] at hu'
        rw [coe_conjS]
        calc LinearMap.trace k V ((u : Module.End k V) * (ρ g * (m : Module.End k V) * ρ g⁻¹))
            = LinearMap.trace k V (ρ g⁻¹ * u * ρ g * (m : Module.End k V)) := by
              rw [LinearMap.trace_mul_comm]
              simp only [mul_assoc]
              rw [LinearMap.trace_mul_comm]
              simp only [mul_assoc]
              rw [LinearMap.trace_mul_comm]
              simp only [mul_assoc]
          _ = 0 := hu'
      refine ⟨m, hmne, fun g => hLline _ (hLconj g), Or.inr fun u hu => ?_⟩
      exact (memL m).1 hmL u hu
  obtain ⟨m, hmne, hχ, hcase⟩ := hkey

  set mE : Module.End k V := (m : Module.End k V) with hmE
  have hmtr : LinearMap.trace k V mE = 0 := (memS _).1 m.2
  have hmEne : mE ≠ 0 := fun h => hmne (Subtype.ext h)
  set d : k := -LinearMap.det mE with hd
  have hmsq : mE * mE = d • 1 := mul_self_eq_smul_one_of_trace_eq_zero hV mE hmtr
  have hχE : ∀ g : H, ∃ χ : k, ρ g * mE * ρ g⁻¹ = χ • mE := by
    intro g
    obtain ⟨χ, hχ⟩ := hχ g
    exact ⟨χ, by have h__af := congrArg Subtype.val hχ; simp at h__af; exact h__af⟩

  have hd0 : d ≠ 0 := by
    intro hd0
    rw [hd0, zero_smul] at hmsq

    let W : Submodule k V := LinearMap.ker mE
    have hst : ∀ g : H, ∀ x ∈ W, ρ g x ∈ W := by
      intro g x hx
      obtain ⟨χ, hχ⟩ := hχE g
      have hχ0 : χ ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hχ
        apply hmEne
        have := congrArg (fun T => ρ g⁻¹ * T * ρ g) hχ
        simp only [mul_zero, zero_mul] at this
        rw [← this, ← mul_assoc, ← mul_assoc, rho_inv_mul, one_mul, mul_assoc, rho_inv_mul,
          mul_one]
      have h1 : ρ g * mE = χ • (mE * ρ g) := by
        have := congrArg (fun T => T * ρ g) hχ
        rw [mul_assoc, rho_inv_mul, mul_one, smul_mul_assoc] at this
        exact this
      rw [LinearMap.mem_ker] at hx ⊢
      have h2 := LinearMap.congr_fun h1 x
      simp only [Module.End.mul_apply, hx, map_zero, LinearMap.smul_apply] at h2
      exact (smul_eq_zero.1 h2.symm).resolve_left hχ0
    rcases hirr W hst with h | h
    ·
      apply hmEne
      apply LinearMap.ext
      intro v
      have : mE (mE v) = 0 := by rw [← Module.End.mul_apply, hmsq, LinearMap.zero_apply]
      have hv : mE v ∈ W := this
      rw [h] at hv
      simpa using hv
    · apply hmEne
      exact LinearMap.ker_eq_top.1 h

  have hpm : ∀ g : H, ρ g * mE = mE * ρ g ∨ ρ g * mE = -(mE * ρ g) := by
    intro g
    obtain ⟨χ, hχ⟩ := hχE g
    have hχsq : χ * χ = 1 := by
      have h1 : (ρ g * mE * ρ g⁻¹) * (ρ g * mE * ρ g⁻¹) = d • 1 := by
        calc (ρ g * mE * ρ g⁻¹) * (ρ g * mE * ρ g⁻¹)
            = ρ g * mE * (ρ g⁻¹ * ρ g) * mE * ρ g⁻¹ := by simp only [mul_assoc]
          _ = ρ g * (mE * mE) * ρ g⁻¹ := by rw [rho_inv_mul, mul_one]; simp only [mul_assoc]
          _ = d • 1 := by rw [hmsq, mul_smul_comm, mul_one, smul_mul_assoc, rho_mul_inv]
      rw [hχ, smul_mul_smul_comm, hmsq, smul_smul] at h1
      have := smul_one_injective hV h1

      have h' : (χ * χ - 1) * d = 0 := by linear_combination this
      exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hd0)
    have hmul : ρ g * mE = χ • (mE * ρ g) := by
      have := congrArg (fun T => T * ρ g) hχ
      rw [mul_assoc, rho_inv_mul, mul_one, smul_mul_assoc] at this
      exact this
    rcases mul_self_eq_one_iff.1 hχsq with h | h
    · left; rw [hmul, h, one_smul]
    · right; rw [hmul, h, neg_one_smul]

  have htr_anti : ∀ g : H, ρ g * mE = -(mE * ρ g) → LinearMap.trace k V (ρ g) = 0 := by
    intro g hg
    have hA : ρ g * mE * mE = -(mE * (ρ g * mE)) := by
      conv_lhs => rw [hg]
      rw [neg_mul, mul_assoc]
    have h1 : LinearMap.trace k V (ρ g * mE * mE) = - LinearMap.trace k V (ρ g * mE * mE) := by
      conv_lhs => rw [hA]
      rw [map_neg, LinearMap.trace_mul_comm]
    have h2' : LinearMap.trace k V (ρ g * mE * mE) = 0 := by
      have : (2 : k) * LinearMap.trace k V (ρ g * mE * mE) = 0 := by linear_combination h1
      exact (mul_eq_zero.1 this).resolve_left h2
    rw [mul_assoc, hmsq, mul_smul_comm, mul_one, map_smul, smul_eq_mul] at h2'
    exact (mul_eq_zero.1 h2').resolve_left hd0
  have hreg_anti : ∀ g : H, ρ g * mE = -(mE * ρ g) → IsReg ρ g :=
    fun g hg => isReg_of_trace_eq_zero h2 hV hsplit (htr_anti g hg)
  have hmemU'_anti : ∀ (g : H) (hg : ρ g * mE = -(mE * ρ g)),
      (⟨ρ g, (memS _).2 (htr_anti g hg)⟩ : S) ∈ U' :=
    fun g hg => Submodule.subset_span ⟨g, hreg_anti g hg, rfl⟩

  have hnotboth : ∀ g : H, ρ g * mE = mE * ρ g → ρ g * mE = -(mE * ρ g) → False := by
    intro g h1 h2'
    apply hmEne
    have h3 : (2 : k) • (ρ g * mE) = 0 := by
      rw [two_smul]; nth_rewrite 2 [h2']; rw [h1, add_neg_cancel]
    rw [smul_eq_zero] at h3
    have h4 := h3.resolve_left h2
    have := congrArg (fun T => ρ g⁻¹ * T) h4
    simp only [mul_zero] at this
    rw [← mul_assoc, rho_inv_mul, one_mul] at this
    exact this

  apply false_of_forall_commute hV hirr ⟨α₀, β₀, hαβ₀, hchar₀⟩
  rcases hcase with ⟨hmz, hline⟩ | horth
  ·
    intro g
    have hcommg : ρ g * mE = mE * ρ g := by
      rcases hpm g with h | h
      · exact h
      · exfalso
        obtain ⟨c, hc⟩ := hline _ (hmemU'_anti g h)
        have hc' : ρ g = c • mE := by simpa using congrArg Subtype.val hc
        apply hnotboth g ?_ h
        rw [hc', smul_mul_assoc, mul_smul_comm]

    have hmz' : mE = ρ h₀ - ((α₀ + β₀) / 2) • 1 := by
      rw [hmE, hmz]
    rw [hmz', mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul] at hcommg
    simpa using hcommg
  ·

    have hnc : ∀ g : H, ρ g * mE = mE * ρ g → ¬ IsReg ρ g := by
      intro g hg hreg
      have hmem : m ∈ U' := Submodule.subset_span ⟨g, hreg, hg.symm⟩
      have h0 := horth m hmem
      rw [← hmE, hmsq, map_smul, LinearMap.trace_one, hV, smul_eq_mul] at h0
      apply hd0
      have : d * 2 = 0 := by exact_mod_cast h0
      exact (mul_eq_zero.1 this).resolve_right h2

    have hsc : ∀ g : H, ρ g * mE = mE * ρ g → ∃ μ : k, ρ g = μ • 1 := by
      intro g hg
      obtain ⟨μ, hμ⟩ := exists_charpoly_eq_sq_of_not_isReg hsplit (hnc g hg)
      refine ⟨μ, ?_⟩
      by_contra hne
      have hn : ρ g - μ • 1 ≠ 0 := fun h => hne (sub_eq_zero.1 h)
      have hnsq := sub_smul_one_mul_self_eq_zero hV hμ
      have hcomm : mE * (ρ g - μ • 1) = (ρ g - μ • 1) * mE := by
        rw [mul_sub, sub_mul, ← hg, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
      have := mul_self_eq_zero_of_commute_nilpotent h2 hV hn hnsq hcomm hmtr
      rw [hmsq] at this
      apply hd0
      have h1 := smul_one_injective hV (this.trans (zero_smul k (1 : Module.End k V)).symm)
      exact h1

    have hh₀a : ρ h₀ * mE = -(mE * ρ h₀) := by
      rcases hpm h₀ with h | h
      · exact absurd ⟨α₀, β₀, hαβ₀, hchar₀⟩ (hnc h₀ h)
      · exact h
    intro g
    rcases hpm g with hg | hg
    · obtain ⟨μ, hμ⟩ := hsc g hg
      rw [hμ, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    ·
      have hgh : ρ (g * h₀) * mE = mE * ρ (g * h₀) := by
        rw [map_mul, mul_assoc, hh₀a, mul_neg, ← mul_assoc, hg, neg_mul, neg_neg, mul_assoc]
      obtain ⟨μ, hμ⟩ := hsc _ hgh
      have hg' : ρ g = μ • ρ h₀⁻¹ := by
        calc ρ g = ρ g * ρ h₀ * ρ h₀⁻¹ := by rw [mul_assoc, rho_mul_inv, mul_one]
          _ = μ • (1 : Module.End k V) * ρ h₀⁻¹ := by rw [← map_mul ρ, hμ]
          _ = μ • ρ h₀⁻¹ := by rw [smul_mul_assoc, one_mul]
      rw [hg', smul_mul_assoc, mul_smul_comm, rho_inv_mul, rho_mul_inv]

end Main

end P2mGrp
p2m_reactivate "P2MW.S_Module_End_exists_charpoly_eq_and_commute_and_trace_eq_zero_and_notMem_of_irreducible.P2mGrp"

end
p2m_reactivate "P2MW.S_Module_End_exists_charpoly_eq_and_commute_and_trace_eq_zero_and_notMem_of_irreducible.P2mGrp"

theorem solution
    {k : Type u} [Field k] (h2 : (2 : k) ≠ 0)
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hV : Module.finrank k V = 2)
    {H : Type w} [Group H] (ρ : H →* Module.End k V)
    (hirr : ∀ W : Submodule k V, (∀ h : H, ∀ x ∈ W, ρ h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hsplit : ∀ h : H, ∃ α β : k, (ρ h).charpoly = (X - C α) * (X - C β))
    (U : AddSubgroup (Module.End k V))
    (hU : ∀ h : H, ∀ m ∈ U, ρ h * m * ρ h⁻¹ ∈ U)
    (hproper : ∃ m : Module.End k V, LinearMap.trace k V m = 0 ∧ m ∉ U) :
    ∃ h : H, ∃ α β : k, α ≠ β ∧ (ρ h).charpoly = (X - C α) * (X - C β) ∧
      ∃ m : Module.End k V, LinearMap.trace k V m = 0 ∧ m * ρ h = ρ h * m ∧ m ∉ U :=
  P2mGrp.main h2 hV hirr hsplit U hU hproper

end S_Module_End_exists_charpoly_eq_and_commute_and_trace_eq_zero_and_notMem_of_irreducible
end P2MW
export P2MW.S_Module_End_exists_charpoly_eq_and_commute_and_trace_eq_zero_and_notMem_of_irreducible (solution)
