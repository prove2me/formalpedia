-- Prove2me | solution 1 for KatzModularForm.constantCoeff_ne_one_of_weight_two_zmod_eight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/5da4a141-2336-56b8-af40-9112e49475bf

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_KatzModularForm_constantCoeff_ne_one_of_weight_two_zmod_eight

noncomputable section

open WeierstrassCurve Polynomial

namespace MazurFiveSixC

universe u

@[reducible] def instCoeFunLaurentPolynomial {R : Type*} [Semiring R] :
    CoeFun (LaurentPolynomial R) (fun _ => ℤ → R) := ⟨fun p => ⇑p.coeff⟩
attribute [local instance] instCoeFunLaurentPolynomial

theorem eight_eq_zero (A : Type*) [Ring A] [Algebra (ZMod 8) A] : (8 : A) = 0 := by
  rw [← map_ofNat (algebraMap (ZMod 8) A) 8]
  exact (congrArg _ (by decide : (8 : ZMod 8) = 0)).trans (map_zero _)

def toAlgHom8 {A B : Type*} [CommRing A] [CommRing B] [Algebra (ZMod 8) A] [Algebra (ZMod 8) B]
    (f : A →+* B) : A →ₐ[ZMod 8] B :=
  { f with
    commutes' := fun r => by
      have h := Subsingleton.elim (f.comp (algebraMap (ZMod 8) A)) (algebraMap (ZMod 8) B)
      exact RingHom.congr_fun h r }

@[scoped simp] theorem coe_toAlgHom8 {A B : Type*} [CommRing A] [CommRing B] [Algebra (ZMod 8) A]
    [Algebra (ZMod 8) B] (f : A →+* B) : ((toAlgHom8 f : A →ₐ[ZMod 8] B) : A →+* B) = f :=
  RingHom.ext fun _ => rfl

theorem toAlgHom8_apply {A B : Type*} [CommRing A] [CommRing B] [Algebra (ZMod 8) A]
    [Algebra (ZMod 8) B] (f : A →+* B) (a : A) : toAlgHom8 f a = f a := rfl

variable (F : KatzModularForm (ZMod 8) 2)

theorem toFun_congr {A : Type} [CommRing A] [Algebra (ZMod 8) A] {W W' : WeierstrassCurve A}
    (h : W = W') (hW : IsUnit W.Δ) (hW' : IsUnit W'.Δ) : F.toFun W hW = F.toFun W' hW' := by
  subst h; rfl

theorem toFun_map (F : KatzModularForm (ZMod 8) 2) {A B : Type} [CommRing A] [CommRing B]
    [Algebra (ZMod 8) A] [Algebra (ZMod 8) B] (f : A →+* B) (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) (hW' : IsUnit (W.map f).Δ) :
    F.toFun (W.map f) hW' = f (F.toFun W hW) := by
  have h := F.map_toFun (toAlgHom8 f) W hW (by simpa using hW')
  simp at h
  exact h

theorem toFun_smul (F : KatzModularForm (ZMod 8) 2) {A : Type} [CommRing A] [Algebra (ZMod 8) A]
    (C : VariableChange A) (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (hW' : IsUnit (C • W).Δ) :
    F.toFun (C • W) hW' = (↑C.u⁻¹ : A) ^ 2 * F.toFun W hW := by
  rw [F.toFun_variableChange C W hW hW']
  norm_cast

def rInv {A : Type} [CommRing A] [Algebra (ZMod 8) A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (β : A) : A :=
  F.toFun W hW * (β + 12 * W.b₄ * β ^ 3)

theorem rInv_congr {A : Type} [CommRing A] [Algebra (ZMod 8) A] {W W' : WeierstrassCurve A}
    (h : W = W') (hW : IsUnit W.Δ) (hW' : IsUnit W'.Δ) (β : A) :
    rInv F W hW β = rInv F W' hW' β := by
  subst h; rfl

theorem rInv_variableChange {A : Type} [CommRing A] [Algebra (ZMod 8) A] (C : VariableChange A)
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (hW' : IsUnit (C • W).Δ) (β β' : A)
    (hβ : β * W.b₂ = 1) (hβ' : β' * (C • W).b₂ = 1) :
    rInv F (C • W) hW' β' = rInv F W hW β := by
  have h8 := eight_eq_zero A
  unfold rInv
  rw [toFun_smul F C W hW hW', variableChange_b₄]
  rw [variableChange_b₂] at hβ'
  generalize F.toFun W hW = Fv at *
  generalize (↑C.u⁻¹ : A) = v at *
  generalize W.b₂ = b₂ at *
  generalize W.b₄ = b₄ at *
  generalize C.r = r at *
  grind

theorem rInv_map {A B : Type} [CommRing A] [CommRing B] [Algebra (ZMod 8) A] [Algebra (ZMod 8) B]
    (f : A →+* B) (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (hW' : IsUnit (W.map f).Δ) (β : A) :
    rInv F (W.map f) hW' (f β) = f (rInv F W hW β) := by
  unfold rInv
  rw [toFun_map F f W hW hW', map_b₄]
  simp [map_ofNat]

theorem isUnit_b₂_of {A : Type} [CommRing A] [Algebra (ZMod 8) A] (W : WeierstrassCurve A)
    {ι : A} (hι : ι * W.a₁ = 1) : IsUnit W.b₂ := by
  have h8 := eight_eq_zero A
  refine IsUnit.of_mul_eq_one (ι ^ 2 * (1 - 4 * W.a₂ * ι ^ 2)) ?_
  simp only [b₂]
  grind

theorem isUnit_b₂_variableChange {A : Type} [CommRing A] [Algebra (ZMod 8) A]
    (C : VariableChange A) (W : WeierstrassCurve A) (h : IsUnit W.b₂) : IsUnit (C • W).b₂ := by
  have h8 := eight_eq_zero A
  obtain ⟨β, hβ⟩ := h.exists_left_inv
  rw [variableChange_b₂]
  refine ((C.u⁻¹).isUnit.pow 2).mul (IsUnit.of_mul_eq_one (β * (1 - 12 * C.r * β)) ?_)
  generalize W.b₂ = b₂ at *
  generalize C.r = r
  grind

def Junit {A : Type} [CommRing A] (W : WeierstrassCurve A) (ι δ : A) (hι : ι * W.a₁ = 1)
    (hδ : δ * W.Δ = 1) : Aˣ where
  val := W.a₁ ^ 12 * δ
  inv := W.Δ * ι ^ 12
  val_inv := by linear_combination (W.a₁ ^ 12 * ι ^ 12) * hδ +
      (ι^11*W.a₁^11 + ι^10*W.a₁^10 + ι^9*W.a₁^9 + ι^8*W.a₁^8 + ι^7*W.a₁^7 + ι^6*W.a₁^6 +
        ι^5*W.a₁^5 + ι^4*W.a₁^4 + ι^3*W.a₁^3 + ι^2*W.a₁^2 + ι*W.a₁ + 1) * hι
  inv_val := by linear_combination (W.a₁ ^ 12 * ι ^ 12) * hδ +
      (ι^11*W.a₁^11 + ι^10*W.a₁^10 + ι^9*W.a₁^9 + ι^8*W.a₁^8 + ι^7*W.a₁^7 + ι^6*W.a₁^6 +
        ι^5*W.a₁^5 + ι^4*W.a₁^4 + ι^3*W.a₁^3 + ι^2*W.a₁^2 + ι*W.a₁ + 1) * hι

@[scoped simp] theorem val_Junit {A : Type} [CommRing A] (W : WeierstrassCurve A) (ι δ : A)
    (hι : ι * W.a₁ = 1) (hδ : δ * W.Δ = 1) : (Junit W ι δ hι hδ : A) = W.a₁ ^ 12 * δ := rfl

@[scoped simp] theorem val_inv_Junit {A : Type} [CommRing A] (W : WeierstrassCurve A) (ι δ : A)
    (hι : ι * W.a₁ = 1) (hδ : δ * W.Δ = 1) : (↑(Junit W ι δ hι hδ)⁻¹ : A) = W.Δ * ι ^ 12 := rfl

section NormalForm

variable {A : Type} [CommRing A]

def nfR (W : WeierstrassCurve A) (ι : A) : A := -(ι ^ 3 * W.a₃)

def nfA2 (W : WeierstrassCurve A) (ι : A) : A := ι ^ 2 * W.a₂ + 3 * nfR W ι

def nfA4 (W : WeierstrassCurve A) (ι : A) : A :=
  ι ^ 4 * W.a₄ + 2 * nfR W ι * (ι ^ 2 * W.a₂) + 3 * nfR W ι ^ 2

def nfA6 (W : WeierstrassCurve A) (ι : A) : A :=
  ι ^ 6 * W.a₆ + nfR W ι * (ι ^ 4 * W.a₄) + nfR W ι ^ 2 * (ι ^ 2 * W.a₂) + nfR W ι ^ 3

def nfT (W : WeierstrassCurve A) (ι : A) : A :=
  (1 + 4 * nfA2 W ι) * (nfA4 W ι + 12 * nfA4 W ι ^ 2)

def α (W : WeierstrassCurve A) (ι : A) : A := nfA2 W ι - 6 * nfT W ι

def nfA6' (W : WeierstrassCurve A) (ι : A) : A :=
  nfA6 W ι - 2 * nfT W ι * nfA4 W ι + 4 * nfT W ι ^ 2 * nfA2 W ι - 8 * nfT W ι ^ 3 + nfT W ι ^ 2

def C₁ (W : WeierstrassCurve A) (ι : A) (hι : ι * W.a₁ = 1) : VariableChange A :=
  ⟨⟨W.a₁, ι, by rw [mul_comm]; exact hι, hι⟩, 0, 0, 0⟩

def CA (W : WeierstrassCurve A) (ι : A) : VariableChange A := ⟨1, nfR W ι, 0, 0⟩

def CB (W : WeierstrassCurve A) (ι : A) : VariableChange A := ⟨1, -2 * nfT W ι, 0, nfT W ι⟩

@[scoped simp] theorem C₁_u_inv (W : WeierstrassCurve A) (ι : A) (hι : ι * W.a₁ = 1) :
    (((C₁ W ι hι).u⁻¹ : Aˣ) : A) = ι := rfl
@[scoped simp] theorem C₁_r (W : WeierstrassCurve A) (ι : A) (hι : ι * W.a₁ = 1) : (C₁ W ι hι).r = 0 := rfl
@[scoped simp] theorem C₁_s (W : WeierstrassCurve A) (ι : A) (hι : ι * W.a₁ = 1) : (C₁ W ι hι).s = 0 := rfl
@[scoped simp] theorem C₁_t (W : WeierstrassCurve A) (ι : A) (hι : ι * W.a₁ = 1) : (C₁ W ι hι).t = 0 := rfl
@[scoped simp] theorem CA_u (W : WeierstrassCurve A) (ι : A) : (CA W ι).u = 1 := rfl
@[scoped simp] theorem CA_r (W : WeierstrassCurve A) (ι : A) : (CA W ι).r = nfR W ι := rfl
@[scoped simp] theorem CA_s (W : WeierstrassCurve A) (ι : A) : (CA W ι).s = 0 := rfl
@[scoped simp] theorem CA_t (W : WeierstrassCurve A) (ι : A) : (CA W ι).t = 0 := rfl
@[scoped simp] theorem CB_u (W : WeierstrassCurve A) (ι : A) : (CB W ι).u = 1 := rfl
@[scoped simp] theorem CB_r (W : WeierstrassCurve A) (ι : A) : (CB W ι).r = -2 * nfT W ι := rfl
@[scoped simp] theorem CB_s (W : WeierstrassCurve A) (ι : A) : (CB W ι).s = 0 := rfl
@[scoped simp] theorem CB_t (W : WeierstrassCurve A) (ι : A) : (CB W ι).t = nfT W ι := rfl

theorem normalForm_eq [Algebra (ZMod 8) A] (W : WeierstrassCurve A) (ι : A) (hι : ι * W.a₁ = 1) :
    CB W ι • (CA W ι • (C₁ W ι hι • W)) = ⟨1, α W ι, 0, 0, nfA6' W ι⟩ := by
  have h8 := eight_eq_zero A
  ext
  · simp only [variableChange_a₁, CB_u, CA_u, C₁_u_inv, inv_one, Units.val_one, CB_s, CA_s, C₁_s]
    linear_combination hι
  · simp only [variableChange_a₂, variableChange_a₁, CB_u, CA_u, C₁_u_inv, inv_one, Units.val_one,
      CB_s, CA_s, C₁_s, CB_r, CA_r, C₁_r, α, nfA2]
    ring
  · simp only [variableChange_a₃, variableChange_a₁, CB_u, CA_u, C₁_u_inv, inv_one, Units.val_one,
      CA_s, C₁_s, CB_r, CA_r, C₁_r, CB_t, CA_t, C₁_t, nfR]
    generalize nfT W ι = T
    generalize W.a₁ = a₁ at *
    generalize W.a₃ = a₃ at *
    grind
  · simp only [variableChange_a₄, variableChange_a₃, variableChange_a₂, variableChange_a₁, CB_u, CA_u,
      C₁_u_inv, inv_one, Units.val_one, CB_s, CA_s, C₁_s, CB_r, CA_r, C₁_r, CB_t, CA_t, C₁_t]
    simp only [nfT, nfA4, nfA2, nfR]
    generalize W.a₁ = a₁ at *
    generalize W.a₂ = a₂ at *
    generalize W.a₃ = a₃ at *
    generalize W.a₄ = a₄ at *
    grind
  · simp only [variableChange_a₆, variableChange_a₄, variableChange_a₃, variableChange_a₂,
      variableChange_a₁, CB_u, CA_u, C₁_u_inv, inv_one, Units.val_one, CA_s, C₁_s, CB_r, CA_r,
      C₁_r, CB_t, CA_t, C₁_t]
    simp only [nfA6', nfA6, nfT, nfA4, nfA2, nfR]
    generalize W.a₁ = a₁ at *
    generalize W.a₂ = a₂ at *
    generalize W.a₃ = a₃ at *
    generalize W.a₄ = a₄ at *
    generalize W.a₆ = a₆ at *
    grind

theorem normalForm_Δ (W : WeierstrassCurve A) (ι : A) (hι : ι * W.a₁ = 1) :
    (CB W ι • (CA W ι • (C₁ W ι hι • W))).Δ = ι ^ 12 * W.Δ := by
  simp only [variableChange_Δ, CB_u, CA_u, C₁_u_inv, inv_one, Units.val_one, one_pow, one_mul]

end NormalForm

abbrev P1 : Type := Polynomial (ZMod 8)

abbrev U : Type := LaurentPolynomial P1

def NU : WeierstrassCurve U :=
  ⟨1, LaurentPolynomial.C (Polynomial.X : P1), 0, 0,
    -(1 + 4 * LaurentPolynomial.C (Polynomial.X : P1)) * (LaurentPolynomial.T (-1) : U)⟩

theorem NU_Δ : NU.Δ = LaurentPolynomial.T (-1) := by
  have h8 := eight_eq_zero U
  simp only [NU, Δ, b₂, b₄, b₆, b₈]
  generalize LaurentPolynomial.C (Polynomial.X : P1) = x at *
  generalize (LaurentPolynomial.T (-1) : U) = y at *
  grind

theorem isUnit_NU_Δ : IsUnit NU.Δ := by
  rw [NU_Δ]; exact LaurentPolynomial.isUnit_T _

def βU : U := 1 + 4 * LaurentPolynomial.C (Polynomial.X : P1)

theorem βU_mul_b₂ : βU * NU.b₂ = 1 := by
  have h8 := eight_eq_zero U
  simp only [βU, NU, b₂]
  generalize LaurentPolynomial.C (Polynomial.X : P1) = x at *
  grind

def ρU : U := rInv F NU isUnit_NU_Δ βU

theorem rInv_normalForm {A : Type} [CommRing A] [Algebra (ZMod 8) A] (W : WeierstrassCurve A)
    (h1 : W.a₁ = 1) (h3 : W.a₃ = 0) (h4 : W.a₄ = 0) (hW : IsUnit W.Δ) (β δ : A)
    (hβ : β * W.b₂ = 1) (hι : (1 : A) * W.a₁ = 1) (hδ : δ * W.Δ = 1) :
    rInv F W hW β =
      LaurentPolynomial.eval₂ (aeval W.a₂).toRingHom (Junit W 1 δ hι hδ) (ρU F) := by
  have h8 := eight_eq_zero A
  set J := Junit W 1 δ hι hδ with hJdef
  set φ : U →+* A := LaurentPolynomial.eval₂ (aeval W.a₂).toRingHom J with hφdef
  have hφC : ∀ p : P1, φ (LaurentPolynomial.C p) = aeval W.a₂ p := fun p => by
    simp [hφdef, LaurentPolynomial.eval₂_C]
  have hφX : φ (LaurentPolynomial.C Polynomial.X) = W.a₂ := by rw [hφC]; simp
  have hφT : φ (LaurentPolynomial.T (-1)) = W.Δ := by
    rw [hφdef, LaurentPolynomial.eval₂_T, zpow_neg_one, hJdef, val_inv_Junit]; ring
  have hΔW : W.Δ = -(1 + 4 * W.a₂) ^ 3 * W.a₆ - 432 * W.a₆ ^ 2 := by
    simp only [Δ, b₂, b₄, b₆, b₈, h1, h3, h4]; ring
  have hmap : NU.map φ = W := by
    ext
    · simp [NU, WeierstrassCurve.map, h1]
    · simp [NU, WeierstrassCurve.map, hφX]
    · simp [NU, WeierstrassCurve.map, h3]
    · simp [NU, WeierstrassCurve.map, h4]
    · simp only [NU, WeierstrassCurve.map, map_neg, map_mul, map_add, map_one, map_ofNat, hφX, hφT,
        hΔW]
      generalize W.a₂ = a₂
      generalize W.a₆ = a₆
      grind
  have hWΔ' : IsUnit (NU.map φ).Δ := by rw [hmap]; exact hW
  have hβ' : β = φ βU := by
    have : φ βU = 1 + 4 * W.a₂ := by
      simp only [βU, map_add, map_one, map_mul, map_ofNat, hφX]
    rw [this]
    have hb2 : W.b₂ = 1 + 4 * W.a₂ := by simp [b₂, h1]
    rw [hb2] at hβ
    linear_combination (1 + 4 * W.a₂) * hβ - β * (W.a₂ + 2 * W.a₂ ^ 2) * h8
  show rInv F W hW β = φ (rInv F NU isUnit_NU_Δ βU)
  rw [rInv_congr F hmap.symm hW hWΔ', hβ']
  exact rInv_map F φ NU isUnit_NU_Δ hWΔ' βU

theorem rInv_eq_eval₂ {A : Type} [CommRing A] [Algebra (ZMod 8) A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) (ι δ β : A) (hι : ι * W.a₁ = 1) (hδ : δ * W.Δ = 1) (hβ : β * W.b₂ = 1) :
    rInv F W hW β =
      LaurentPolynomial.eval₂ (aeval (α W ι)).toRingHom (Junit W ι δ hι hδ) (ρU F) := by
  have h8 := eight_eq_zero A
  have hb : IsUnit W.b₂ := isUnit_b₂_of W hι

  have hW₁ : IsUnit (C₁ W ι hι • W).Δ := KatzModularForm.isUnit_Δ_variableChange _ hW
  have hW₂ : IsUnit (CA W ι • (C₁ W ι hι • W)).Δ := KatzModularForm.isUnit_Δ_variableChange _ hW₁
  have hW₃ : IsUnit (CB W ι • (CA W ι • (C₁ W ι hι • W))).Δ :=
    KatzModularForm.isUnit_Δ_variableChange _ hW₂
  have hb₁ : IsUnit (C₁ W ι hι • W).b₂ := isUnit_b₂_variableChange _ W hb
  have hb₂ : IsUnit (CA W ι • (C₁ W ι hι • W)).b₂ := isUnit_b₂_variableChange _ _ hb₁
  have hb₃ : IsUnit (CB W ι • (CA W ι • (C₁ W ι hι • W))).b₂ := isUnit_b₂_variableChange _ _ hb₂
  obtain ⟨β₁, hβ₁⟩ := hb₁.exists_left_inv
  obtain ⟨β₂, hβ₂⟩ := hb₂.exists_left_inv
  obtain ⟨β₃, hβ₃⟩ := hb₃.exists_left_inv
  have e1 := (rInv_variableChange F (C₁ W ι hι) W hW hW₁ β β₁ hβ hβ₁).symm
  have e2 := (rInv_variableChange F (CA W ι) _ hW₁ hW₂ β₁ β₂ hβ₁ hβ₂).symm
  have e3 := (rInv_variableChange F (CB W ι) _ hW₂ hW₃ β₂ β₃ hβ₂ hβ₃).symm
  have hnf := normalForm_eq W ι hι
  set W₃ := CB W ι • (CA W ι • (C₁ W ι hι • W)) with hW₃def
  have h1 : W₃.a₁ = 1 := by rw [hnf]
  have h2 : W₃.a₂ = α W ι := by rw [hnf]
  have h3 : W₃.a₃ = 0 := by rw [hnf]
  have h4 : W₃.a₄ = 0 := by rw [hnf]
  have hι1 : (1 : A) * W₃.a₁ = 1 := by rw [h1, one_mul]
  have hΔ₃ : W₃.Δ = ι ^ 12 * W.Δ := normalForm_Δ W ι hι
  have hδ₃ : (W.a₁ ^ 12 * δ) * W₃.Δ = 1 := by
    rw [hΔ₃]
    linear_combination (W.a₁ ^ 12 * ι ^ 12) * hδ +
      (ι^11*W.a₁^11 + ι^10*W.a₁^10 + ι^9*W.a₁^9 + ι^8*W.a₁^8 + ι^7*W.a₁^7 + ι^6*W.a₁^6 +
        ι^5*W.a₁^5 + ι^4*W.a₁^4 + ι^3*W.a₁^3 + ι^2*W.a₁^2 + ι*W.a₁ + 1) * hι
  have e4 := rInv_normalForm F W₃ h1 h3 h4 hW₃ β₃ (W.a₁ ^ 12 * δ) hβ₃ hι1 hδ₃
  have hJ : Junit W₃ 1 (W.a₁ ^ 12 * δ) hι1 hδ₃ = Junit W ι δ hι hδ := by
    ext; simp [h1]
  rw [e1, e2, e3, e4, hJ, h2]

section LaurentAux

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

theorem eval₂_eq_sum (f : R →+* S) (x : Sˣ) (p : LaurentPolynomial R) :
    LaurentPolynomial.eval₂ f x p = ∑ b ∈ p.coeff.support, f (p b) * ((x ^ b : Sˣ) : S) := by
  have hp : p.coeff.sum (fun b a => LaurentPolynomial.C a * LaurentPolynomial.T b) = p := by
    conv_rhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
    exact Finsupp.sum_congr fun b _ => (LaurentPolynomial.single_eq_C_mul_T _ _).symm
  calc LaurentPolynomial.eval₂ f x p = LaurentPolynomial.eval₂ f x (p.coeff.sum fun b a => LaurentPolynomial.C a * LaurentPolynomial.T b) := by
        rw [hp]
    _ = p.coeff.sum fun b a => LaurentPolynomial.eval₂ f x (LaurentPolynomial.C a * LaurentPolynomial.T b) := map_finsuppSum _ _ _
    _ = _ := Finset.sum_congr rfl fun b _ => by
      show LaurentPolynomial.eval₂ f x (LaurentPolynomial.C (p b) * LaurentPolynomial.T b) = _
      rw [LaurentPolynomial.eval₂_C_mul_T]

variable (R) in

def Tunit : (LaurentPolynomial R)ˣ := ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1), by rw [← LaurentPolynomial.T_add]; simp, by rw [← LaurentPolynomial.T_add]; simp⟩

theorem Tunit_zpow (b : ℤ) : ((Tunit R ^ b : (LaurentPolynomial R)ˣ) : LaurentPolynomial R) = LaurentPolynomial.T b := by
  rcases b with n | n
  · simp [Tunit, LaurentPolynomial.T_pow]
  · rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    show LaurentPolynomial.T (-1) ^ (n + 1) = _
    rw [LaurentPolynomial.T_pow, Int.negSucc_eq]; congr 1; push_cast; ring

theorem C_mul_T_apply (r : R) (n b : ℤ) : (LaurentPolynomial.C r * LaurentPolynomial.T n : LaurentPolynomial R) b = if n = b then r else 0 := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single]; exact Finsupp.single_apply

end LaurentAux

section HasseTaylor

theorem hasseDeriv_map {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (n : ℕ)
    (p : R[X]) : hasseDeriv n (p.map f) = (hasseDeriv n p).map f := by
  ext i
  simp [hasseDeriv_coeff, coeff_map]

abbrev P2 : Type := Polynomial P1

def Xc : P2 := Polynomial.C Polynomial.X

def sv : P2 := Polynomial.X

def Xsub : P2 := (1 - 2 * sv + 4 * sv ^ 2) ^ 2 * (Xc - sv - sv ^ 2)

def hOne : P2 := Xc * (-4 + 12 * sv - 16 * sv ^ 2 + 16 * sv ^ 3) - (1 + sv) * (1 - 2 * sv + 4 * sv ^ 2) ^ 2

theorem Xsub_eq : Xsub = Xc + sv * hOne := by
  simp only [Xsub, hOne]; ring

theorem eval_zero_hOne : hOne.eval 0 = -(4 * Polynomial.X + 1) := by
  simp [hOne, Xc, sv]; ring

theorem isUnit_eval_zero_hOne : IsUnit (hOne.eval 0) := by
  have h8 := eight_eq_zero P1
  rw [eval_zero_hOne]
  refine IsUnit.of_mul_eq_one (4 * Polynomial.X - 1) ?_
  linear_combination (-2 * (Polynomial.X : P1) ^ 2) * h8

theorem eval_map_Xc (q : P1) : (q.map (algebraMap (ZMod 8) P2)).eval Xc = Polynomial.C q := by
  have halg : algebraMap (ZMod 8) P2 = (Polynomial.C : P1 →+* P2).comp Polynomial.C := by
    ext r
    · simp [Polynomial.algebraMap_apply]
  rw [eval_map, halg, Xc, ← Polynomial.hom_eval₂, eval₂_C_X]

theorem eq_C_of_aeval_Xsub_eq (p : P1) (h : aeval Xsub p = Polynomial.C p) :
    p = Polynomial.C (p.coeff 0) := by

  set n := p.natDegree + 1 with hn
  set D : ℕ → P1 := fun i => hasseDeriv i p with hD
  set y : P2 := sv * hOne with hy
  have hdeg : (taylor Xc (p.map (algebraMap (ZMod 8) P2))).natDegree < n := by
    rw [natDegree_taylor]
    exact lt_of_le_of_lt (natDegree_map_le) (Nat.lt_succ_self _)
  have hsum : ∑ i ∈ Finset.range n, Polynomial.C (D i) * y ^ i = Polynomial.C p := by
    have h1 : aeval Xsub p = (taylor Xc (p.map (algebraMap (ZMod 8) P2))).eval y := by
      rw [taylor_eval, aeval_def, ← eval_map, Xsub_eq, hy, add_comm]
    rw [h1, eval_eq_sum_range' hdeg] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [taylor_coeff, hasseDeriv_map, eval_map_Xc]

  have hDvan : ∀ k, 1 ≤ k → D k = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases hkn : n ≤ k
      · exact hasseDeriv_eq_zero_of_lt_natDegree p k (by omega)
      push Not at hkn

      have hsplit : ∑ i ∈ Finset.range n, Polynomial.C (D i) * y ^ i =
          Polynomial.C p + ∑ i ∈ Finset.Ico k n, Polynomial.C (D i) * y ^ i := by
        rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by omega : 1 ≤ n),
          ← Finset.sum_Ico_consecutive _ hk hkn.le]
        have h0 : ∑ i ∈ Finset.Ico 0 1, Polynomial.C (D i) * y ^ i = Polynomial.C p := by
          simp [hD]
        have hmid : ∑ i ∈ Finset.Ico 1 k, Polynomial.C (D i) * y ^ i = 0 := by
          refine Finset.sum_eq_zero fun i hi => ?_
          rw [Finset.mem_Ico] at hi
          rw [ih i hi.2 hi.1, map_zero, zero_mul]
        rw [h0, hmid, zero_add]
      have htail : ∑ i ∈ Finset.Ico k n, Polynomial.C (D i) * y ^ i = 0 := by
        have := hsum; rw [hsplit] at this; simpa using this

      set Q : P2 := ∑ i ∈ Finset.Ico k n, Polynomial.C (D i) * y ^ (i - k) with hQ
      have hfac : sv ^ k * (hOne ^ k * Q) = 0 := by
        rw [← htail, hQ, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_Ico] at hi
        rw [show y ^ i = y ^ k * y ^ (i - k) by rw [← pow_add, Nat.add_sub_cancel' hi.1], hy]
        ring
      have hreg : hOne ^ k * Q = 0 :=
        (Polynomial.isRegular_X_pow (R := P1) k).left
          (show sv ^ k * (hOne ^ k * Q) = sv ^ k * 0 by rw [mul_zero]; exact hfac)

      have hQ0 : ∑ i ∈ Finset.Ico k n, eval 0 (Polynomial.C (D i) * y ^ (i - k)) = D k := by
        rw [Finset.sum_eq_single_of_mem k (Finset.mem_Ico.mpr ⟨le_rfl, hkn⟩)]
        · simp
        · intro i hi hik
          rw [Finset.mem_Ico] at hi
          have hpos : 0 < i - k := by omega
          simp [hy, sv, zero_pow hpos.ne']
      have hev : (hOne.eval 0) ^ k * D k = 0 := by
        have := congrArg (Polynomial.eval (0 : P1)) hreg
        rwa [eval_mul, eval_pow, eval_zero, hQ, eval_finsetSum, hQ0] at this
      exact (isUnit_eval_zero_hOne.pow k).mul_right_eq_zero.mp hev

  have hnat : p.natDegree = 0 := by
    by_contra hne
    have hpos : 1 ≤ p.natDegree := Nat.one_le_iff_ne_zero.mpr hne
    have h0 : D p.natDegree = 0 := hDvan _ hpos
    have hcoeff : (D p.natDegree).coeff 0 = p.coeff p.natDegree := by
      simp [hD, hasseDeriv_coeff]
    have hlead : p.coeff p.natDegree ≠ 0 := by
      rw [← leadingCoeff, Ne, leadingCoeff_eq_zero]
      rintro rfl
      exact hne (natDegree_zero)
    rw [h0, coeff_zero] at hcoeff
    exact hlead hcoeff.symm
  exact eq_C_of_natDegree_eq_zero hnat

end HasseTaylor

section Residual

abbrev B : Type := LaurentPolynomial P2

def WB : WeierstrassCurve B :=
  ⟨1, LaurentPolynomial.C Xc, 0, 0, -(1 + 4 * LaurentPolynomial.C Xc) * (LaurentPolynomial.T (-1) : B)⟩

theorem WB_Δ : WB.Δ = LaurentPolynomial.T (-1) := by
  have h8 := eight_eq_zero B
  simp only [WB, Δ, b₂, b₄, b₆, b₈]
  generalize LaurentPolynomial.C Xc = x at *
  generalize (LaurentPolynomial.T (-1) : B) = y at *
  grind

theorem isUnit_WB_Δ : IsUnit WB.Δ := by rw [WB_Δ]; exact LaurentPolynomial.isUnit_T _

def us : Bˣ :=
  ⟨LaurentPolynomial.C (1 + 2 * sv), LaurentPolynomial.C (1 - 2 * sv + 4 * sv ^ 2),
    by
      have h8 := eight_eq_zero B
      rw [← map_mul]; rw [show (1 + 2 * sv) * (1 - 2 * sv + 4 * sv ^ 2) = 1 + 8 * sv ^ 3 by ring]
      rw [map_add, map_one, map_mul, map_ofNat, h8, zero_mul, add_zero],
    by
      have h8 := eight_eq_zero B
      rw [← map_mul]; rw [show (1 - 2 * sv + 4 * sv ^ 2) * (1 + 2 * sv) = 1 + 8 * sv ^ 3 by ring]
      rw [map_add, map_one, map_mul, map_ofNat, h8, zero_mul, add_zero]⟩

def Cs : VariableChange B := ⟨us, 0, LaurentPolynomial.C sv, 0⟩

theorem Cs_WB_a₁ : (Cs • WB).a₁ = 1 := by
  simp only [variableChange_a₁, Cs, WB, us, Units.inv_mk]
  have h8 := eight_eq_zero B
  rw [show (LaurentPolynomial.C (1 - 2 * sv + 4 * sv ^ 2) : B) * (1 + 2 * LaurentPolynomial.C sv) = LaurentPolynomial.C ((1 - 2 * sv + 4 * sv ^ 2) *
    (1 + 2 * sv)) by simp [map_mul, map_add, map_ofNat]]
  rw [show (1 - 2 * sv + 4 * sv ^ 2) * (1 + 2 * sv) = 1 + 8 * sv ^ 3 by ring]
  rw [map_add, map_one, map_mul, map_ofNat, h8, zero_mul, add_zero]

theorem Cs_WB_a₂ : (Cs • WB).a₂ = LaurentPolynomial.C Xsub := by
  simp only [variableChange_a₂, Cs, WB, us, Units.inv_mk, Xsub]
  simp [map_mul, map_sub, map_add, map_pow, map_ofNat]

theorem Cs_WB_a₃ : (Cs • WB).a₃ = 0 := by
  simp [variableChange_a₃, Cs, WB]

theorem Cs_WB_a₄ : (Cs • WB).a₄ = 0 := by
  simp [variableChange_a₄, Cs, WB]

theorem Cs_WB_Δ : (Cs • WB).Δ = LaurentPolynomial.T (-1) := by
  have h8 := eight_eq_zero B
  rw [variableChange_Δ, WB_Δ]
  simp only [Cs, us, Units.inv_mk]
  have hpow : (LaurentPolynomial.C (1 - 2 * sv + 4 * sv ^ 2) : B) ^ 12 = 1 := by
    rw [map_add, map_sub, map_one, map_mul, map_mul, map_ofNat, map_ofNat, map_pow]
    generalize (LaurentPolynomial.C sv : B) = x
    grind
  rw [hpow, one_mul]

theorem eval₂_aeval_C_eq_mapRingHom (y : P2) :
    LaurentPolynomial.eval₂ (aeval (R := ZMod 8) (LaurentPolynomial.C y : B)).toRingHom (Tunit P2) =
      AddMonoidAlgebra.mapRingHom ℤ (aeval (R := ZMod 8) y).toRingHom := by
  refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
  · rw [AddMonoidAlgebra.mapRingHom_single, LaurentPolynomial.single_eq_C,
      LaurentPolynomial.single_eq_C, LaurentPolynomial.eval₂_C]
    show aeval (toAlgHom8 (LaurentPolynomial.C : P2 →+* B) y) r = LaurentPolynomial.C (aeval y r)
    rw [aeval_algHom_apply]
    rfl
  · rw [AddMonoidAlgebra.mapRingHom_single, map_one]
    have h1 : (AddMonoidAlgebra.single m (1 : P1) : U) = LaurentPolynomial.T m := by
      rw [LaurentPolynomial.single_eq_C_mul_T, map_one, one_mul]
    have h2 : (AddMonoidAlgebra.single m (1 : P2) : B) = LaurentPolynomial.T m := by
      rw [LaurentPolynomial.single_eq_C_mul_T, map_one, one_mul]
    rw [h1, h2, LaurentPolynomial.eval₂_T, Tunit_zpow]

theorem aeval_Xc (q : P1) : aeval Xc q = Polynomial.C q := by
  change aeval ((toAlgHom8 (Polynomial.C : P1 →+* P2)) Polynomial.X) q = _
  rw [aeval_algHom_apply, aeval_X_left_apply]
  rfl

theorem aeval_Xsub_ρU (b : ℤ) : aeval Xsub (ρU F b) = Polynomial.C (ρU F b) := by
  have h8 := eight_eq_zero B

  have hι : (1 : B) * WB.a₁ = 1 := by simp [WB]
  have hδ : LaurentPolynomial.T 1 * WB.Δ = 1 := by
    rw [WB_Δ, ← LaurentPolynomial.T_add]; simp
  have hb2 : WB.b₂ = 1 + 4 * LaurentPolynomial.C Xc := by simp [WB, b₂]
  have hβ : (1 + 4 * LaurentPolynomial.C Xc) * WB.b₂ = 1 := by
    rw [hb2]
    generalize (LaurentPolynomial.C Xc : B) = x
    grind
  have hbu : IsUnit WB.b₂ := isUnit_b₂_of WB hι

  have hW' : IsUnit (Cs • WB).Δ := by rw [Cs_WB_Δ]; exact LaurentPolynomial.isUnit_T _
  have hι' : (1 : B) * (Cs • WB).a₁ = 1 := by rw [Cs_WB_a₁, one_mul]
  have hδ' : LaurentPolynomial.T 1 * (Cs • WB).Δ = 1 := by
    rw [Cs_WB_Δ, ← LaurentPolynomial.T_add]; simp
  obtain ⟨β', hβ'⟩ := (isUnit_b₂_variableChange Cs WB hbu).exists_left_inv

  have e0 := rInv_variableChange F Cs WB isUnit_WB_Δ hW' _ β' hβ hβ'
  have e1 := rInv_eq_eval₂ F WB isUnit_WB_Δ 1 (LaurentPolynomial.T 1) _ hι hδ hβ
  have e2 := rInv_eq_eval₂ F (Cs • WB) hW' 1 (LaurentPolynomial.T 1) β' hι' hδ' hβ'
  have hα1 : α WB 1 = LaurentPolynomial.C Xc := by
    simp only [α, nfA2, nfT, nfA4, nfR, WB]; ring
  have hα2 : α (Cs • WB) 1 = LaurentPolynomial.C Xsub := by
    simp only [α, nfA2, nfT, nfA4, nfR, Cs_WB_a₂, Cs_WB_a₃, Cs_WB_a₄]; ring
  have hJ1 : Junit WB 1 (LaurentPolynomial.T 1) hι hδ = Tunit P2 := by
    ext; simp [WB, Tunit]
  have hJ2 : Junit (Cs • WB) 1 (LaurentPolynomial.T 1) hι' hδ' = Tunit P2 := by
    ext; simp [Cs_WB_a₁, Tunit]
  rw [hα1, hJ1, eval₂_aeval_C_eq_mapRingHom] at e1
  rw [hα2, hJ2, eval₂_aeval_C_eq_mapRingHom, e0, e1] at e2
  have := congrArg (fun q : B => q b) e2
  simp only [AddMonoidAlgebra.coeff_mapRingHom, RingHom.coe_coe, AlgHom.toRingHom_eq_coe] at this
  rw [aeval_Xc] at this
  exact this.symm

theorem ρU_eq_C (b : ℤ) : ρU F b = Polynomial.C ((ρU F b).coeff 0) :=
  eq_C_of_aeval_Xsub_eq _ (aeval_Xsub_ρU F b)

end Residual

def cst (b : ℤ) : ZMod 8 := (ρU F b).coeff 0

theorem rInv_eq_sum {A : Type} [CommRing A] [Algebra (ZMod 8) A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) (ι δ β : A) (hι : ι * W.a₁ = 1) (hδ : δ * W.Δ = 1) (hβ : β * W.b₂ = 1) :
    rInv F W hW β = ∑ b ∈ (ρU F).coeff.support,
      algebraMap (ZMod 8) A (cst F b) * ((Junit W ι δ hι hδ ^ b : Aˣ) : A) := by
  rw [rInv_eq_eval₂ F W hW ι δ β hι hδ hβ, eval₂_eq_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  conv_lhs => rw [ρU_eq_C F b]
  simp [cst]

theorem cst_ne_zero_of_mem {b : ℤ} (hb : b ∈ (ρU F).coeff.support) : cst F b ≠ 0 := by
  intro h
  have h1 := ρU_eq_C F b
  rw [show (ρU F b).coeff 0 = cst F b from rfl, h, map_zero] at h1
  exact (Finsupp.mem_support_iff.mp hb) h1

section HahnAux

variable {R : Type} [CommRing R]

local notation "L" => LaurentSeries R

private theorem _root_.MazurFiveSixC.coeff_C_mul (c : R) (x : L) (n : ℤ) : (HahnSeries.C c * x).coeff n = c * x.coeff n := by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]

p2m_export "MazurFiveSixC" "coeff_C_mul"
theorem coeff_single_one_mul (b n : ℤ) (x : L) :
    (HahnSeries.single b (1 : R) * x).coeff n = x.coeff (n - b) := by
  rw [HahnSeries.coeff_single_mul, one_mul]

theorem coeff_mul_single_one (b n : ℤ) (x : L) :
    (x * HahnSeries.single b (1 : R)).coeff n = x.coeff (n - b) := by
  rw [HahnSeries.coeff_mul_single, mul_one]

theorem coeff_ofPowerSeries (x : PowerSeries R) (k : ℤ) :
    (HahnSeries.ofPowerSeries ℤ R x).coeff k = if 0 ≤ k then PowerSeries.coeff k.toNat x else 0 := by
  split_ifs with hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, Int.toNat_natCast]
  · exact ModularCurve.ofPowerSeries_coeff_of_neg x (lt_of_not_ge hk)

theorem coeff_ofPowerSeries_zero (x : PowerSeries R) :
    (HahnSeries.ofPowerSeries ℤ R x).coeff 0 = PowerSeries.constantCoeff x := by
  rw [coeff_ofPowerSeries, if_pos le_rfl, Int.toNat_zero, PowerSeries.coeff_zero_eq_constantCoeff]

theorem coeff_ofPowerSeries_of_neg (x : PowerSeries R) {k : ℤ} (hk : k < 0) :
    (HahnSeries.ofPowerSeries ℤ R x).coeff k = 0 := by
  rw [coeff_ofPowerSeries, if_neg (not_le.mpr hk)]

theorem val_zpow_of_eq_single_mul (J : Lˣ) (ω : (PowerSeries R)ˣ) (m : ℤ)
    (hJ : (J : L) = HahnSeries.single m 1 * HahnSeries.ofPowerSeries ℤ R ω)
    (hJ' : (↑J⁻¹ : L) = HahnSeries.single (-m) 1 * HahnSeries.ofPowerSeries ℤ R ↑ω⁻¹) (b : ℤ) :
    ((J ^ b : Lˣ) : L) =
      HahnSeries.single (b * m) 1 * HahnSeries.ofPowerSeries ℤ R ↑(ω ^ b) := by
  rcases b with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, hJ, mul_pow,
      HahnSeries.single_pow, one_pow, ← map_pow, Units.val_pow_eq_pow_val, nsmul_eq_mul]
  · rw [zpow_negSucc, zpow_negSucc, ← inv_pow, ← inv_pow, Units.val_pow_eq_pow_val, hJ', mul_pow,
      HahnSeries.single_pow, one_pow, ← map_pow, Units.val_pow_eq_pow_val, nsmul_eq_mul,
      Int.negSucc_eq]
    congr 2
    push_cast
    ring_nf

theorem constantCoeff_units_zpow (ω : (PowerSeries R)ˣ) (b : ℤ) :
    PowerSeries.constantCoeff (↑(ω ^ b) : PowerSeries R) =
      ↑((Units.map (PowerSeries.constantCoeff : PowerSeries R →+* R).toMonoidHom ω) ^ b) := by
  rw [← map_zpow, Units.coe_map]; rfl

theorem algebraMap_zmod8_laurent (c : ZMod 8) :
    algebraMap (ZMod 8) (LaurentSeries (ZMod 8)) c = HahnSeries.C c :=
  RingHom.congr_fun (Subsingleton.elim (algebraMap (ZMod 8) (LaurentSeries (ZMod 8))) HahnSeries.C) c

end HahnAux

section Tate

open ModularCurve

scoped instance : Fact (1 < 8) := ⟨by norm_num⟩

local notation "R8" => ZMod 8
local notation "L8" => LaurentSeries (ZMod 8)

theorem tate_Δ_eq : ∃ u : PowerSeries ℤ, PowerSeries.constantCoeff u = 1 ∧
    tatePowerSeries.Δ = PowerSeries.X * u := by
  have hΔeq : tatePowerSeries.Δ =
      -tateA6 + tateA4 ^ 2 - PowerSeries.C 64 * tateA4 ^ 3 - PowerSeries.C 432 * tateA6 ^ 2
        + PowerSeries.C 72 * (tateA4 * tateA6) := by
    rw [show (PowerSeries.C (64 : ℤ)) = (64 : PowerSeries ℤ) from map_ofNat _ 64,
      show (PowerSeries.C (432 : ℤ)) = (432 : PowerSeries ℤ) from map_ofNat _ 432,
      show (PowerSeries.C (72 : ℤ)) = (72 : PowerSeries ℤ) from map_ofNat _ 72]
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, tatePowerSeries_a₁, tatePowerSeries_a₂, tatePowerSeries_a₃,
      tatePowerSeries_a₄, tatePowerSeries_a₆]
    ring
  have hc0 : PowerSeries.constantCoeff tatePowerSeries.Δ = 0 := by
    rw [hΔeq]
    simp only [map_add, map_sub, map_neg, map_mul, map_pow, PowerSeries.constantCoeff_C,
      constantCoeff_tateA4, constantCoeff_tateA6]
    ring
  have hmul1 : ∀ f g : PowerSeries ℤ, PowerSeries.coeff 1 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 1 g +
        PowerSeries.coeff 1 f * PowerSeries.coeff 0 g := by
    intro f g
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have h420 : PowerSeries.coeff 0 (tateA4 ^ 2) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_tateA4]
    norm_num
  have hsq4 : PowerSeries.coeff 1 (tateA4 ^ 2) = 0 := by
    rw [pow_two, hmul1, coeff_zero_tateA4]
    norm_num
  have hsq6 : PowerSeries.coeff 1 (tateA6 ^ 2) = 0 := by
    rw [pow_two, hmul1, coeff_zero_tateA6]
    norm_num
  have hcb4 : PowerSeries.coeff 1 (tateA4 ^ 3) = 0 := by
    rw [show tateA4 ^ 3 = tateA4 ^ 2 * tateA4 from pow_succ tateA4 2, hmul1, h420, hsq4,
      coeff_zero_tateA4]
    norm_num
  have hprod : PowerSeries.coeff 1 (tateA4 * tateA6) = 0 := by
    rw [hmul1, coeff_zero_tateA4, coeff_zero_tateA6]
    norm_num
  have hc1 : PowerSeries.coeff 1 tatePowerSeries.Δ = 1 := by
    rw [hΔeq]
    simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, hsq4, hsq6, hcb4, hprod,
      coeff_one_tateA6]
    norm_num
  obtain ⟨u, hXu⟩ : (PowerSeries.X : PowerSeries ℤ) ∣ tatePowerSeries.Δ :=
    PowerSeries.X_dvd_iff.mpr hc0
  refine ⟨u, ?_, hXu⟩
  rw [← hc1, hXu, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul]

theorem support_le_zero_and_cst_zero (g : PowerSeries R8)
    (hg : F.qExpansion = HahnSeries.ofPowerSeries ℤ R8 g) (hg1 : PowerSeries.constantCoeff g = 1) :
    (∀ b ∈ (ρU F).coeff.support, b ≤ 0) ∧ (0 : ℤ) ∈ (ρU F).coeff.support ∧ cst F 0 = 1 := by
  have h8 := eight_eq_zero L8
  set W : WeierstrassCurve L8 := tateLaurent R8 with hWdef
  have hW : IsUnit W.Δ := W.isUnit_Δ

  obtain ⟨u, hu1, hXu⟩ := tate_Δ_eq
  set uR : PowerSeries R8 := u.map (Int.castRingHom R8) with huR
  have huR1 : PowerSeries.constantCoeff uR = 1 := by
    rw [huR, ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hu1, map_one]
  have huRu : IsUnit uR := by rw [PowerSeries.isUnit_iff_constantCoeff, huR1]; exact isUnit_one
  set ωD : (PowerSeries R8)ˣ := huRu.unit with hωD
  have hΔ : W.Δ = HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ R8 ↑ωD := by
    rw [hWdef, tateLaurent, WeierstrassCurve.map_Δ, hXu, map_mul, laurentOfInt_apply, laurentOfInt_apply,
      PowerSeries.map_X, HahnSeries.ofPowerSeries_X, hωD, IsUnit.unit_spec]

  have ha1 : W.a₁ = 1 := by simp [hWdef, tateLaurent, tatePowerSeries, WeierstrassCurve.map]
  have ha3 : W.a₃ = 0 := by simp [hWdef, tateLaurent, tatePowerSeries, WeierstrassCurve.map]
  have hb2 : W.b₂ = 1 := by
    simp [hWdef, tateLaurent, tatePowerSeries, WeierstrassCurve.map, WeierstrassCurve.b₂]
  have hι : (1 : L8) * W.a₁ = 1 := by rw [ha1, one_mul]
  have hβ : (1 : L8) * W.b₂ = 1 := by rw [hb2, one_mul]
  set δ : L8 := HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ R8 ↑ωD⁻¹ with hδdef
  have hδ : δ * W.Δ = 1 := by
    rw [hΔ, hδdef, mul_mul_mul_comm, HahnSeries.single_mul_single, ← map_mul, Units.inv_mul, map_one]
    simp

  have hr : rInv F W hW 1 = HahnSeries.ofPowerSeries ℤ R8 g := by
    have hb4 : W.b₄ = 2 * W.a₄ := by
      simp only [WeierstrassCurve.b₄, ha1, ha3]; ring
    have h24 : (12 : L8) * (2 * W.a₄) * 1 ^ 3 = 3 * W.a₄ * 8 := by ring
    rw [rInv, hb4, h24, h8, mul_zero, add_zero, mul_one, ← hg]
    rfl

  set J := Junit W 1 δ hι hδ with hJdef
  have hJ : (J : L8) = HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ R8 ↑ωD⁻¹ := by
    rw [hJdef, val_Junit, ha1, one_pow, one_mul]
  have hJ' : (↑J⁻¹ : L8) = HahnSeries.single (-(-1) : ℤ) 1 * HahnSeries.ofPowerSeries ℤ R8 ↑ωD⁻¹⁻¹ := by
    rw [hJdef, val_inv_Junit, one_pow, mul_one, hΔ, inv_inv, neg_neg]
  have hJb := val_zpow_of_eq_single_mul J ωD⁻¹ (-1) hJ hJ'

  have hmain := rInv_eq_sum F W hW 1 δ 1 hι hδ hβ
  rw [hr] at hmain
  have hcoeff : ∀ n : ℤ, (HahnSeries.ofPowerSeries ℤ R8 g).coeff n =
      ∑ b ∈ (ρU F).coeff.support, cst F b * (HahnSeries.ofPowerSeries ℤ R8 ↑(ωD⁻¹ ^ b)).coeff (n + b) := by
    intro n
    rw [hmain, HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [algebraMap_zmod8_laurent, coeff_C_mul, hJb, coeff_single_one_mul]
    congr 2; ring
  have hcc : ∀ b : ℤ, PowerSeries.constantCoeff (↑(ωD⁻¹ ^ b) : PowerSeries R8) = 1 := by
    intro b
    rw [constantCoeff_units_zpow]
    have h1 : Units.map (PowerSeries.constantCoeff : PowerSeries R8 →+* R8).toMonoidHom ωD = 1 := by
      ext; simp [hωD, huR1]
    have : Units.map (PowerSeries.constantCoeff : PowerSeries R8 →+* R8).toMonoidHom ωD⁻¹ = 1 := by
      rw [map_inv, h1, inv_one]
    rw [this, one_zpow, Units.val_one]
  have hS : (ρU F).coeff.support.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have := hcoeff 0
    rw [hemp, Finset.sum_empty, coeff_ofPowerSeries_zero, hg1] at this
    exact one_ne_zero this

  have hA : ∀ b ∈ (ρU F).coeff.support, b ≤ 0 := by
    set M := (ρU F).coeff.support.max' hS with hM
    have hMmem : M ∈ (ρU F).coeff.support := Finset.max'_mem _ _
    have hle : ∀ b ∈ (ρU F).coeff.support, b ≤ M := fun b hb => Finset.le_max' _ _ hb
    by_contra hcon
    push Not at hcon
    obtain ⟨b₀, hb₀, hb₀pos⟩ := hcon
    have hMpos : 0 < M := lt_of_lt_of_le hb₀pos (hle b₀ hb₀)
    have := hcoeff (-M)
    rw [coeff_ofPowerSeries_of_neg _ (by omega), Finset.sum_eq_single_of_mem M hMmem] at this
    · rw [neg_add_cancel, coeff_ofPowerSeries_zero, hcc, mul_one] at this
      exact cst_ne_zero_of_mem F hMmem this.symm
    · intro b hb hbM
      rw [coeff_ofPowerSeries_of_neg _ (by have := hle b hb; omega), mul_zero]

  have hB : (0 : ℤ) ∈ (ρU F).coeff.support ∧ cst F 0 = 1 := by
    have h0 := hcoeff 0
    rw [coeff_ofPowerSeries_zero, hg1] at h0
    by_cases hmem : (0 : ℤ) ∈ (ρU F).coeff.support
    · rw [Finset.sum_eq_single_of_mem 0 hmem] at h0
      · rw [zero_add, coeff_ofPowerSeries_zero, hcc, mul_one] at h0
        exact ⟨hmem, h0.symm⟩
      · intro b hb hb0
        have hblt : b < 0 := lt_of_le_of_ne (hA b hb) hb0
        rw [zero_add, coeff_ofPowerSeries_of_neg _ hblt, mul_zero]
    · rw [Finset.sum_eq_zero] at h0
      · exact absurd h0 one_ne_zero
      · intro b hb
        have hblt : b < 0 := lt_of_le_of_ne (hA b hb) (fun h => hmem (h ▸ hb))
        rw [zero_add, coeff_ofPowerSeries_of_neg _ hblt, mul_zero]
  exact ⟨hA, hB⟩

end Tate

section TestFamily

local notation "R8" => ZMod 8
local notation "P8" => PowerSeries (ZMod 8)
local notation "L8" => LaurentSeries (ZMod 8)

def EP : WeierstrassCurve P8 := ⟨PowerSeries.X, 0, 1, 0, 0⟩

theorem EP_Δ : EP.Δ = PowerSeries.X ^ 3 - 27 := by
  simp only [EP, Δ, b₂, b₄, b₆, b₈]; ring

theorem isUnit_EP_Δ : IsUnit EP.Δ := by
  rw [PowerSeries.isUnit_iff_constantCoeff, EP_Δ, map_sub, map_pow, PowerSeries.constantCoeff_X,
    map_ofNat, zero_pow three_ne_zero, zero_sub]
  exact IsUnit.of_mul_eq_one (-27 : R8) (by decide)

def EL : WeierstrassCurve L8 := EP.map (HahnSeries.ofPowerSeries ℤ R8)

theorem isUnit_EL_Δ : IsUnit EL.Δ := KatzModularForm.isUnit_Δ_map _ isUnit_EP_Δ

theorem EL_a₁ : EL.a₁ = HahnSeries.single (1 : ℤ) 1 := by
  simp [EL, EP, WeierstrassCurve.map]
theorem EL_a₂ : EL.a₂ = 0 := by simp [EL, EP, WeierstrassCurve.map]
theorem EL_a₃ : EL.a₃ = 1 := by simp [EL, EP, WeierstrassCurve.map]
theorem EL_a₄ : EL.a₄ = 0 := by simp [EL, EP, WeierstrassCurve.map]

theorem twelve_ne_zero_zmod8 : (12 : R8) ≠ 0 := by decide

theorem main_contradiction (hA : ∀ b ∈ (ρU F).coeff.support, b ≤ 0) (h0 : (0 : ℤ) ∈ (ρU F).coeff.support)
    (hc0 : cst F 0 = 1) : False := by
  have h8 := eight_eq_zero L8

  set φE : P8 := F.toFun EP isUnit_EP_Δ with hφE
  have hFE : F.toFun EL isUnit_EL_Δ = HahnSeries.ofPowerSeries ℤ R8 φE :=
    toFun_map F (HahnSeries.ofPowerSeries ℤ R8) EP isUnit_EP_Δ isUnit_EL_Δ

  have hdE : IsUnit (PowerSeries.X ^ 3 - 27 : P8) := EP_Δ ▸ isUnit_EP_Δ
  set ωE : P8ˣ := hdE.unit with hωE
  have hΔ : EL.Δ = HahnSeries.ofPowerSeries ℤ R8 ↑ωE := by
    rw [EL, WeierstrassCurve.map_Δ, EP_Δ, hωE, IsUnit.unit_spec]
  set ι : L8 := HahnSeries.single (-1 : ℤ) 1 with hιdef
  have hι : ι * EL.a₁ = 1 := by
    rw [EL_a₁, hιdef, HahnSeries.single_mul_single]; simp
  set δ : L8 := HahnSeries.ofPowerSeries ℤ R8 ↑ωE⁻¹ with hδdef
  have hδ : δ * EL.Δ = 1 := by
    rw [hΔ, hδdef, ← map_mul, Units.inv_mul, map_one]
  have hb2 : EL.b₂ = HahnSeries.single (2 : ℤ) 1 := by
    rw [WeierstrassCurve.b₂, EL_a₁, EL_a₂, HahnSeries.single_pow]; simp
  set β : L8 := HahnSeries.single (-2 : ℤ) 1 with hβdef
  have hβ : β * EL.b₂ = 1 := by
    rw [hb2, hβdef, HahnSeries.single_mul_single]; simp
  have hb4 : EL.b₄ = HahnSeries.single (1 : ℤ) 1 := by
    rw [WeierstrassCurve.b₄, EL_a₁, EL_a₃, EL_a₄]; simp

  have hr : rInv F EL isUnit_EL_Δ β = HahnSeries.ofPowerSeries ℤ R8 φE *
      (HahnSeries.single (-2 : ℤ) 1 + 12 * HahnSeries.single (-5 : ℤ) 1) := by
    rw [rInv, hFE, hb4, hβdef, HahnSeries.single_pow, mul_assoc (12 : L8), HahnSeries.single_mul_single]
    norm_num

  set J := Junit EL ι δ hι hδ with hJdef
  have hJ : (J : L8) = HahnSeries.single (12 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ R8 ↑ωE⁻¹ := by
    rw [hJdef, val_Junit, EL_a₁, HahnSeries.single_pow]; simp [hδdef]
  have hJ' : (↑J⁻¹ : L8) = HahnSeries.single (-12 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ R8 ↑ωE⁻¹⁻¹ := by
    rw [hJdef, val_inv_Junit, hΔ, inv_inv, hιdef, HahnSeries.single_pow, mul_comm]; simp
  have hJb := val_zpow_of_eq_single_mul J ωE⁻¹ 12 hJ hJ'

  have hmain := rInv_eq_sum F EL isUnit_EL_Δ ι δ β hι hδ hβ
  rw [hr] at hmain
  have hcoeff : ∀ n : ℤ, (HahnSeries.ofPowerSeries ℤ R8 φE).coeff (n + 2) +
      12 * (HahnSeries.ofPowerSeries ℤ R8 φE).coeff (n + 5) =
      ∑ b ∈ (ρU F).coeff.support, cst F b * (HahnSeries.ofPowerSeries ℤ R8 ↑(ωE⁻¹ ^ b)).coeff (n - 12 * b) := by
    intro n
    have := congrArg (fun x : L8 => x.coeff n) hmain
    simp only [HahnSeries.coeff_sum] at this
    rw [mul_add, HahnSeries.coeff_add, coeff_mul_single_one, ← mul_assoc, mul_comm _ (12 : L8), mul_assoc,
      show (12 : L8) = HahnSeries.C 12 from (map_ofNat _ 12).symm, coeff_C_mul, coeff_mul_single_one] at this
    rw [show n - -2 = n + 2 by ring, show n - -5 = n + 5 by ring] at this
    rw [this]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [algebraMap_zmod8_laurent, coeff_C_mul, hJb, coeff_single_one_mul]
    congr 2; ring
  have hS : (ρU F).coeff.support.Nonempty := ⟨0, h0⟩
  set m := (ρU F).coeff.support.min' hS with hm
  have hmmem : m ∈ (ρU F).coeff.support := Finset.min'_mem _ _
  have hmle : ∀ b ∈ (ρU F).coeff.support, m ≤ b := fun b hb => Finset.min'_le _ _ hb
  have hm0 : m ≤ 0 := hmle 0 h0
  rcases hm0.lt_or_eq with hmneg | hmzero
  ·
    have h := hcoeff (12 * m)
    rw [coeff_ofPowerSeries_of_neg _ (by omega), coeff_ofPowerSeries_of_neg _ (by omega), mul_zero,
      add_zero, Finset.sum_eq_single_of_mem m hmmem] at h
    · rw [sub_self, coeff_ofPowerSeries_zero, constantCoeff_units_zpow] at h
      exact cst_ne_zero_of_mem F hmmem ((Units.mul_left_eq_zero _).mp h.symm)
    · intro b hb hbm
      have : m < b := lt_of_le_of_ne (hmle b hb) (Ne.symm hbm)
      rw [coeff_ofPowerSeries_of_neg _ (by omega), mul_zero]
  ·
    have honly : ∀ b ∈ (ρU F).coeff.support, b = 0 := fun b hb =>
      le_antisymm (hA b hb) (hmzero ▸ hmle b hb)
    have hsum : ∀ n : ℤ, ∑ b ∈ (ρU F).coeff.support,
        cst F b * (HahnSeries.ofPowerSeries ℤ R8 ↑(ωE⁻¹ ^ b)).coeff (n - 12 * b) =
        (HahnSeries.ofPowerSeries ℤ R8 (1 : P8)).coeff n := by
      intro n
      rw [Finset.sum_eq_single_of_mem 0 h0 (fun b hb hb0 => (hb0 (honly b hb)).elim), hc0, one_mul,
        zpow_zero, Units.val_one, mul_zero, sub_zero]
    have e1 := hcoeff (-3)
    rw [hsum, coeff_ofPowerSeries_of_neg φE (show (-3 : ℤ) + 2 < 0 by norm_num),
      coeff_ofPowerSeries_of_neg (1 : P8) (show (-3 : ℤ) < 0 by norm_num), zero_add,
      show ((-3 : ℤ) + 5) = 0 + 2 by norm_num] at e1
    have e2 := hcoeff 0
    rw [hsum, coeff_ofPowerSeries_zero, map_one] at e2

    have e3 : (12 : R8) * ((HahnSeries.ofPowerSeries ℤ R8 φE).coeff (0 + 2) +
        12 * (HahnSeries.ofPowerSeries ℤ R8 φE).coeff (0 + 5)) = 12 := by rw [e2, mul_one]
    rw [mul_add, e1, zero_add, ← mul_assoc, show (12 * 12 : R8) = 0 by decide, zero_mul] at e3
    exact twelve_ne_zero_zmod8 e3.symm

end TestFamily

end MazurFiveSixC
p2m_reactivate "P2MW.S_KatzModularForm_constantCoeff_ne_one_of_weight_two_zmod_eight.MazurFiveSixC"

theorem solution (F : KatzModularForm (ZMod 8) 2) (g : PowerSeries (ZMod 8))
    (hg : F.qExpansion = HahnSeries.ofPowerSeries ℤ (ZMod 8) g) :
    PowerSeries.constantCoeff g ≠ 1 := fun hg1 =>
  let ⟨hA, h0, hc0⟩ := MazurFiveSixC.support_le_zero_and_cst_zero F g hg hg1
  MazurFiveSixC.main_contradiction F hA h0 hc0

end
end S_KatzModularForm_constantCoeff_ne_one_of_weight_two_zmod_eight
end P2MW
export P2MW.S_KatzModularForm_constantCoeff_ne_one_of_weight_two_zmod_eight (solution)
