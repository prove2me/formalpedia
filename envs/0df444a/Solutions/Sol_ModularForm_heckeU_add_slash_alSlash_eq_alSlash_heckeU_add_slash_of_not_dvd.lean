-- Prove2me | solution 1 for ModularForm.heckeU_add_slash_alSlash_eq_alSlash_heckeU_add_slash_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/16e573ff-0023-577e-9a1a-b0f393cfc820

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_heckeU_add_slash_alSlash_eq_alSlash_heckeU_add_slash_of_not_dvd

set_option autoImplicit false

open scoped MatrixGroups ModularForm
open Matrix

namespace FALT

def C11 (Q R a b ℓ j : ℤ) : ℤ := Q * a - Q * R * a * j - R * b * ℓ
def C12 (Q a b ℓ j : ℤ) : ℤ := Q * a ^ 2 * j + a * b * (ℓ - 1)
def C21 (R M ℓ j : ℤ) : ℤ := M * (1 - R * j - ℓ)
def C22 (Q R M a b ℓ j : ℤ) : ℤ := M * a * j + Q * a * ℓ - R * b
def E11 (Q R a b ℓ : ℤ) : ℤ := Q * a * ℓ - R * b
def E12 (a b ℓ : ℤ) : ℤ := a * b * (1 - ℓ)
def E21 (M ℓ : ℤ) : ℤ := M * (ℓ - 1)
def E22 (Q R a b ℓ : ℤ) : ℤ := Q * a - R * b * ℓ

def gamA (Q R M a b ℓ j c1 c2 : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![C11 Q R a b ℓ j, c1; C21 R M ℓ j, c2]

def gamB (Q R M a b ℓ j c3 c4 : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![c3, C12 Q a b ℓ j; c4, C22 Q R M a b ℓ j]

def gamC (Q R M a b ℓ c5 c6 : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![E11 Q R a b ℓ, c5; E21 M ℓ, c6]

section identities

variable (Q R M a b ℓ : ℤ) (hM : M = Q * R) (hR : R ≠ 0) (hℓ : ℓ ≠ 0) (hbez : Q * a - R * b = 1)
include hM hR hℓ hbez

theorem identity_A (j j' c1 c2 : ℤ) (hc1 : ℓ * c1 = C12 Q a b ℓ j - C11 Q R a b ℓ j * j')
    (hc2 : ℓ * c2 = C22 Q R M a b ℓ j - C21 R M ℓ j * j') :
    (!![(Q : ℝ) * a, b; M, Q] : Matrix (Fin 2) (Fin 2) ℝ) * !![(1 : ℝ), j; 0, ℓ] =
      ((gamA Q R M a b ℓ j c1 c2).map (Int.castRingHom ℝ)) * (!![(1 : ℝ), j'; 0, ℓ] * !![(Q : ℝ) * a, b; M, Q]) := by
  have hRr : (R : ℝ) ≠ 0 := by exact_mod_cast hR
  have hlr : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ
  have hb : (b : ℝ) = ((Q : ℝ) * a - 1) / R := by
    rw [eq_div_iff hRr]; have := congrArg (fun z : ℤ => (z : ℝ)) hbez; push_cast at this; linarith
  have h1 : (c1 : ℝ) = ((C12 Q a b ℓ j : ℤ) - (C11 Q R a b ℓ j : ℤ) * j') / ℓ := by
    rw [eq_div_iff hlr]; have := congrArg (fun z : ℤ => (z : ℝ)) hc1; push_cast at this; linarith
  have h2 : (c2 : ℝ) = ((C22 Q R M a b ℓ j : ℤ) - (C21 R M ℓ j : ℤ) * j') / ℓ := by
    rw [eq_div_iff hlr]; have := congrArg (fun z : ℤ => (z : ℝ)) hc2; push_cast at this; linarith
  have hMr : (M : ℝ) = Q * R := by exact_mod_cast hM
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [gamA, C11, C21, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    (simp only [h1, h2]; push_cast [C11, C12, C21, C22]; simp only [hb, hMr]; field_simp; ring)

theorem det_gamA (j j' c1 c2 : ℤ) (hc1 : ℓ * c1 = C12 Q a b ℓ j - C11 Q R a b ℓ j * j')
    (hc2 : ℓ * c2 = C22 Q R M a b ℓ j - C21 R M ℓ j * j') :
    (gamA Q R M a b ℓ j c1 c2).det = 1 := by
  have hRr : (R : ℝ) ≠ 0 := by exact_mod_cast hR
  have hlr : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ
  have hb : (b : ℝ) = ((Q : ℝ) * a - 1) / R := by
    rw [eq_div_iff hRr]; have := congrArg (fun z : ℤ => (z : ℝ)) hbez; push_cast at this; linarith
  have h1 : (c1 : ℝ) = ((C12 Q a b ℓ j : ℤ) - (C11 Q R a b ℓ j : ℤ) * j') / ℓ := by
    rw [eq_div_iff hlr]; have := congrArg (fun z : ℤ => (z : ℝ)) hc1; push_cast at this; linarith
  have h2 : (c2 : ℝ) = ((C22 Q R M a b ℓ j : ℤ) - (C21 R M ℓ j : ℤ) * j') / ℓ := by
    rw [eq_div_iff hlr]; have := congrArg (fun z : ℤ => (z : ℝ)) hc2; push_cast at this; linarith
  have hMr : (M : ℝ) = Q * R := by exact_mod_cast hM
  apply Int.cast_injective (α := ℝ)
  rw [gamA, Matrix.det_fin_two_of]
  push_cast
  simp only [h1, h2]; push_cast [C11, C12, C21, C22]; simp only [hb, hMr]
  field_simp
  ring

theorem identity_B (j c3 c4 : ℤ) (hc3 : ℓ * c3 = C11 Q R a b ℓ j) (hc4 : ℓ * c4 = C21 R M ℓ j) :
    (!![(Q : ℝ) * a, b; M, Q] : Matrix (Fin 2) (Fin 2) ℝ) * !![(1 : ℝ), j; 0, ℓ] =
      ((gamB Q R M a b ℓ j c3 c4).map (Int.castRingHom ℝ)) * (!![(ℓ : ℝ), 0; 0, 1] * !![(Q : ℝ) * a, b; M, Q]) := by
  have hRr : (R : ℝ) ≠ 0 := by exact_mod_cast hR
  have hlr : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ
  have hb : (b : ℝ) = ((Q : ℝ) * a - 1) / R := by
    rw [eq_div_iff hRr]; have := congrArg (fun z : ℤ => (z : ℝ)) hbez; push_cast at this; linarith
  have h3 : (c3 : ℝ) = ((C11 Q R a b ℓ j : ℤ)) / ℓ := by
    rw [eq_div_iff hlr]; have := congrArg (fun z : ℤ => (z : ℝ)) hc3; push_cast at this; linarith
  have h4 : (c4 : ℝ) = ((C21 R M ℓ j : ℤ)) / ℓ := by
    rw [eq_div_iff hlr]; have := congrArg (fun z : ℤ => (z : ℝ)) hc4; push_cast at this; linarith
  have hMr : (M : ℝ) = Q * R := by exact_mod_cast hM
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [gamB, C12, C22, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    (simp only [h3, h4]; push_cast [C11, C12, C21, C22]; simp only [hb, hMr]; field_simp; ring)

theorem det_gamB (j c3 c4 : ℤ) (hc3 : ℓ * c3 = C11 Q R a b ℓ j) (hc4 : ℓ * c4 = C21 R M ℓ j)
    (hj : ∃ t : ℤ, 1 - R * j = ℓ * t) :
    (gamB Q R M a b ℓ j c3 c4).det = 1 := by
  obtain ⟨t, ht⟩ := hj
  have hRr : (R : ℝ) ≠ 0 := by exact_mod_cast hR
  have hlr : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ
  have hb : (b : ℝ) = ((Q : ℝ) * a - 1) / R := by
    rw [eq_div_iff hRr]; have := congrArg (fun z : ℤ => (z : ℝ)) hbez; push_cast at this; linarith
  have h3 : (c3 : ℝ) = ((C11 Q R a b ℓ j : ℤ)) / ℓ := by
    rw [eq_div_iff hlr]; have := congrArg (fun z : ℤ => (z : ℝ)) hc3; push_cast at this; linarith
  have h4 : (c4 : ℝ) = ((C21 R M ℓ j : ℤ)) / ℓ := by
    rw [eq_div_iff hlr]; have := congrArg (fun z : ℤ => (z : ℝ)) hc4; push_cast at this; linarith
  have hMr : (M : ℝ) = Q * R := by exact_mod_cast hM
  apply Int.cast_injective (α := ℝ)
  rw [gamB, Matrix.det_fin_two_of]
  push_cast
  simp only [h3, h4]; push_cast [C11, C12, C21, C22]; simp only [hb, hMr]
  field_simp
  ring

theorem identity_C (js c5 c6 : ℤ) (hc5 : ℓ * c5 = E12 a b ℓ - E11 Q R a b ℓ * js)
    (hc6 : ℓ * c6 = E22 Q R a b ℓ - E21 M ℓ * js) :
    (!![(Q : ℝ) * a, b; M, Q] : Matrix (Fin 2) (Fin 2) ℝ) * !![(ℓ : ℝ), 0; 0, 1] =
      ((gamC Q R M a b ℓ c5 c6).map (Int.castRingHom ℝ)) * (!![(1 : ℝ), js; 0, ℓ] * !![(Q : ℝ) * a, b; M, Q]) := by
  have hRr : (R : ℝ) ≠ 0 := by exact_mod_cast hR
  have hlr : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ
  have hb : (b : ℝ) = ((Q : ℝ) * a - 1) / R := by
    rw [eq_div_iff hRr]; have := congrArg (fun z : ℤ => (z : ℝ)) hbez; push_cast at this; linarith
  have h5 : (c5 : ℝ) = ((E12 a b ℓ : ℤ) - (E11 Q R a b ℓ : ℤ) * js) / ℓ := by
    rw [eq_div_iff hlr]; have := congrArg (fun z : ℤ => (z : ℝ)) hc5; push_cast at this; linarith
  have h6 : (c6 : ℝ) = ((E22 Q R a b ℓ : ℤ) - (E21 M ℓ : ℤ) * js) / ℓ := by
    rw [eq_div_iff hlr]; have := congrArg (fun z : ℤ => (z : ℝ)) hc6; push_cast at this; linarith
  have hMr : (M : ℝ) = Q * R := by exact_mod_cast hM
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [gamC, E11, E21, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    (simp only [h5, h6]; push_cast [E11, E12, E21, E22]; simp only [hb, hMr]; field_simp; ring)

theorem det_gamC (js c5 c6 : ℤ) (hc5 : ℓ * c5 = E12 a b ℓ - E11 Q R a b ℓ * js)
    (hc6 : ℓ * c6 = E22 Q R a b ℓ - E21 M ℓ * js) :
    (gamC Q R M a b ℓ c5 c6).det = 1 := by
  have hRr : (R : ℝ) ≠ 0 := by exact_mod_cast hR
  have hlr : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ
  have hb : (b : ℝ) = ((Q : ℝ) * a - 1) / R := by
    rw [eq_div_iff hRr]; have := congrArg (fun z : ℤ => (z : ℝ)) hbez; push_cast at this; linarith
  have h5 : (c5 : ℝ) = ((E12 a b ℓ : ℤ) - (E11 Q R a b ℓ : ℤ) * js) / ℓ := by
    rw [eq_div_iff hlr]; have := congrArg (fun z : ℤ => (z : ℝ)) hc5; push_cast at this; linarith
  have h6 : (c6 : ℝ) = ((E22 Q R a b ℓ : ℤ) - (E21 M ℓ : ℤ) * js) / ℓ := by
    rw [eq_div_iff hlr]; have := congrArg (fun z : ℤ => (z : ℝ)) hc6; push_cast at this; linarith
  have hMr : (M : ℝ) = Q * R := by exact_mod_cast hM
  apply Int.cast_injective (α := ℝ)
  rw [gamC, Matrix.det_fin_two_of]
  push_cast
  simp only [h5, h6]; push_cast [E11, E12, E21, E22]; simp only [hb, hMr]
  field_simp
  ring

omit hℓ in

theorem detC (j : ℤ) : C11 Q R a b ℓ j * C22 Q R M a b ℓ j - C12 Q a b ℓ j * C21 R M ℓ j = ℓ := by
  have hRr : (R : ℝ) ≠ 0 := by exact_mod_cast hR
  have hb : (b : ℝ) = ((Q : ℝ) * a - 1) / R := by
    rw [eq_div_iff hRr]; have := congrArg (fun z : ℤ => (z : ℝ)) hbez; push_cast at this; linarith
  have hMr : (M : ℝ) = Q * R := by exact_mod_cast hM
  apply Int.cast_injective (α := ℝ)
  push_cast [C11, C12, C21, C22]; simp only [hb, hMr]
  field_simp
  ring

omit hℓ in
theorem detE : E11 Q R a b ℓ * E22 Q R a b ℓ - E12 a b ℓ * E21 M ℓ = ℓ := by
  have hRr : (R : ℝ) ≠ 0 := by exact_mod_cast hR
  have hb : (b : ℝ) = ((Q : ℝ) * a - 1) / R := by
    rw [eq_div_iff hRr]; have := congrArg (fun z : ℤ => (z : ℝ)) hbez; push_cast at this; linarith
  have hMr : (M : ℝ) = Q * R := by exact_mod_cast hM
  apply Int.cast_injective (α := ℝ)
  push_cast [E11, E12, E21, E22]; simp only [hb, hMr]
  field_simp
  ring

end identities

end FALT

namespace FALT

theorem val_mapGL (g : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (g : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) :=
  Matrix.ext fun _ => congrFun rfl

theorem val_alGL {M Q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M Q) :
    ((W.alGL : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(Q : ℝ) * W.a, W.b; M, Q] := by
  rw [ModularForm.AtkinLehnerDatum.alGL_coe, ModularForm.AtkinLehnerDatum.mat]
  have hM : (M : ℝ) = (Q : ℝ) * W.R := by exact_mod_cast W.hM
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hM]

theorem sum_slash {ι : Type*} (s : Finset ι) (k : ℤ) (g : GL (Fin 2) ℝ) (F : ι → UpperHalfPlane → ℂ) :
    (∑ i ∈ s, F i) ∣[k] g = ∑ i ∈ s, (F i) ∣[k] g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

noncomputable def rep (ℓ : ℕ) (σ : GL (Fin 2) ℝ) : Option (Fin ℓ) → GL (Fin 2) ℝ
  | none => σ * ModularForm.heckeDiagMatrix ℓ
  | some j => ModularForm.heckeMatrix ℓ j

theorem heckeU_add_slash_eq_sum (k : ℤ) (ℓ : ℕ) (σ : GL (Fin 2) ℝ) (f : UpperHalfPlane → ℂ) :
    ModularForm.heckeU k ℓ f + f ∣[k] (σ * ModularForm.heckeDiagMatrix ℓ) =
      ∑ i : Option (Fin ℓ), f ∣[k] rep ℓ σ i := by
  rw [Fintype.sum_option, ModularForm.heckeU_def, add_comm, Finset.sum_range]
  rfl

theorem mul_inv_mem_GammaH {M p : ℕ} [NeZero M] (hpM : p ∣ M) {H : Subgroup (ZMod M)ˣ}
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (γ δ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hδ : δ ∈ CongruenceSubgroup.Gamma0 M)
    (h : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (M / p)) = (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (M / p))) :
    γ * δ⁻¹ ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  have hmem : γ * δ⁻¹ ∈ CongruenceSubgroup.Gamma0 M := Subgroup.mul_mem _ hγ (Subgroup.inv_mem _ hδ)
  refine ⟨hmem, hHp _ ?_⟩
  have hval : CohCarrier.gamma0Units M ⟨γ * δ⁻¹, hmem⟩ =
      CohCarrier.gamma0Units M ⟨γ, hγ⟩ * (CohCarrier.gamma0Units M ⟨δ, hδ⟩)⁻¹ := by
    rw [← map_inv, ← map_mul]; rfl
  have hu : ∀ (τ : SL(2, ℤ)) (hτ : τ ∈ CongruenceSubgroup.Gamma0 M),
      ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (CohCarrier.gamma0Units M ⟨τ, hτ⟩) : (ZMod (M / p))ˣ) : ZMod (M / p)) =
        (((τ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (M / p)) := by
    intro τ hτ
    rw [ZMod.unitsMap_def, Units.coe_map, CohCarrier.val_gamma0Units]
    show ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod (M / p)) ((CongruenceSubgroup.Gamma0Map M) ⟨τ, hτ⟩) = _
    simp only [CongruenceSubgroup.Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, map_intCast]
  have he : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (CohCarrier.gamma0Units M ⟨γ, hγ⟩) =
      ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (CohCarrier.gamma0Units M ⟨δ, hδ⟩) := by
    apply Units.ext; rw [hu, hu]; exact h
  rw [hval, map_mul, map_inv, he, mul_inv_cancel]

theorem slash_mapGL_mul_eq {M p : ℕ} [NeZero M] (hpM : p ∣ M) {H : Subgroup (ZMod M)ˣ}
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) (k : ℤ)
    {f : UpperHalfPlane → ℂ} (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (γ δ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hδ : δ ∈ CongruenceSubgroup.Gamma0 M)
    (h : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (M / p)) = (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (M / p)))
    (A : GL (Fin 2) ℝ) :
    f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) * A) =
      f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ) * A) := by
  have e : (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ (γ * δ⁻¹) : GL (Fin 2) ℝ) * (Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ) := by
    rw [← map_mul, inv_mul_cancel_right]
  rw [e, mul_assoc, SlashAction.slash_mul, hf _ (Subgroup.mem_map_of_mem _ (mul_inv_mem_GammaH hpM hHp γ δ hγ hδ h))]

end FALT

namespace FALT
open ModularForm
variable {M q : ℕ}

open ModularForm

variable {M q : ℕ}

def conjMat (W : AtkinLehnerDatum M q) (A B c' D : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(q : ℤ) * W.a * A + W.b * (M : ℤ) * c' - (W.R : ℤ) * (q : ℤ) * W.a * B - (W.R : ℤ) * W.b * D,
      -(W.a * W.b * A) + (q : ℤ) * W.a ^ 2 * B + W.a * W.b * D - W.b ^ 2 * (W.R : ℤ) * c';
    (M : ℤ) * (A - (W.R : ℤ) * B - D) + (q : ℤ) * (M : ℤ) * c',
      -(W.b * (W.R : ℤ) * A) - W.b * (M : ℤ) * c' + W.a * (M : ℤ) * B + (q : ℤ) * W.a * D]

theorem mat_mul_eq_conjMat_mul (W : AtkinLehnerDatum M q) (A B c' D : ℤ) :
    W.mat * !![A, B; (M : ℤ) * c', D] = conjMat W A B c' D * W.mat := by
  have hM : (M : ℤ) = (q : ℤ) * (W.R : ℤ) := W.hM_int
  have hbz := W.bezout
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AtkinLehnerDatum.mat, conjMat, Matrix.mul_apply, Fin.sum_univ_two, hM]
  · linear_combination (-((q : ℤ) * (W.a * A + W.b * (W.R : ℤ) * c'))) * hbz
  · linear_combination (-((q : ℤ) * W.a * B + W.b * D)) * hbz
  · linear_combination (-((q : ℤ) * (W.R : ℤ) * (A + (q : ℤ) * c'))) * hbz
  · linear_combination (-((q : ℤ) * (W.R : ℤ) * B + (q : ℤ) * D)) * hbz

theorem val_mapGL' (γ : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

theorem exists_conj [NeZero M] (W : AtkinLehnerDatum M q) (σ : SL(2, ℤ))
    (hσ : σ ∈ CongruenceSubgroup.Gamma0 M) :
    ∃ (c' : ℤ) (σ' : SL(2, ℤ)),
      (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (M : ℤ) * c' ∧
      (σ' : Matrix (Fin 2) (Fin 2) ℤ) =
        conjMat W ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0) ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1) c'
          ((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ∧
      σ' ∈ CongruenceSubgroup.Gamma0 M ∧
      W.alGL * (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) =
        (Matrix.SpecialLinearGroup.mapGL ℝ σ' : GL (Fin 2) ℝ) * W.alGL := by
  obtain ⟨c', hc'⟩ : (M : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp (CongruenceSubgroup.Gamma0_mem.mp hσ)
  set A := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with hAdef
  set B := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hBdef
  set D := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hDdef
  have hσe : (σ : Matrix (Fin 2) (Fin 2) ℤ) = !![A, B; (M : ℤ) * c', D] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hAdef, hBdef, hDdef, hc']
  have hmul := mat_mul_eq_conjMat_mul W A B c' D
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (W.q_pos).ne'
  have hdet : (conjMat W A B c' D).det = 1 := by
    have h := congrArg Matrix.det hmul
    rw [Matrix.det_mul, Matrix.det_mul, W.det_mat, ← hσe, σ.2, mul_one] at h
    have h' : (conjMat W A B c' D).det * (q : ℤ) = 1 * (q : ℤ) := by rw [one_mul]; exact h.symm
    exact mul_right_cancel₀ hq0 h'
  refine ⟨c', ⟨conjMat W A B c' D, hdet⟩, hc', rfl, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    show (((M : ℤ) * (A - (W.R : ℤ) * B - D) + (q : ℤ) * (M : ℤ) * c' : ℤ) : ZMod M) = 0
    push_cast
    rw [ZMod.natCast_self]
    ring
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, AtkinLehnerDatum.alGL_coe, val_mapGL', val_mapGL']
    show W.mat.map (algebraMap ℤ ℝ) * ((σ : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ ℝ) =
      (conjMat W A B c' D).map (algebraMap ℤ ℝ) * W.mat.map (algebraMap ℤ ℝ)
    rw [hσe, ← Matrix.map_mul, ← Matrix.map_mul, hmul]

end FALT

open FALT in
theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M (M / p))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (k : ℤ)
    (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 M)
    (hσℓ : (((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M) = ℓ)
    (ρ : SL(2, ℤ)) (hρ : ρ ∈ CongruenceSubgroup.Gamma0 M)
    (hρℓ : (((ρ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (M / p)) * (ℓ : ZMod (M / p)) = 1)
    (f : UpperHalfPlane → ℂ)
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) :
    ModularForm.heckeU k ℓ (ModularForm.alSlash W k f) +
        (ModularForm.alSlash W k f) ∣[k]
          ((Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ) =
      ModularForm.alSlash W k
        (ModularForm.heckeU k ℓ (f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ρ : GL (Fin 2) ℝ)) +
          (f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ρ : GL (Fin 2) ℝ)) ∣[k]
            ((Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ)) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩

  have hR0 : (W.R : ℤ) ≠ 0 := by exact_mod_cast W.R_pos.ne'
  have hMZ : (M : ℤ) = ((M / p : ℕ) : ℤ) * (W.R : ℤ) := W.hM_int
  have hbez : ((M / p : ℕ) : ℤ) * W.a - (W.R : ℤ) * W.b = 1 := W.bezout
  have hℓ0 : ℓ ≠ 0 := hℓ.ne_zero
  have hℓZ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ0
  have hMl : ((M : ℤ) : ZMod ℓ) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd_natCast] at h
    exact hℓM h
  have hRl : ((W.R : ℤ) : ZMod ℓ) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd_natCast] at h
    exact hℓM (h.trans ⟨M / p, W.hM.trans (Nat.mul_comm _ _)⟩)
  have hll : ((ℓ : ℤ) : ZMod ℓ) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr dvd_rfl

  let c11 : Fin ℓ → ℤ := fun t => C11 ((M / p : ℕ) : ℤ) (W.R : ℤ) W.a W.b (ℓ : ℤ) ((t : ℕ) : ℤ)
  let c12 : Fin ℓ → ℤ := fun t => C12 ((M / p : ℕ) : ℤ) W.a W.b (ℓ : ℤ) ((t : ℕ) : ℤ)
  let c21 : Fin ℓ → ℤ := fun t => C21 (W.R : ℤ) (M : ℤ) (ℓ : ℤ) ((t : ℕ) : ℤ)
  let c22 : Fin ℓ → ℤ := fun t => C22 ((M / p : ℕ) : ℤ) (W.R : ℤ) (M : ℤ) W.a W.b (ℓ : ℤ) ((t : ℕ) : ℤ)
  let e11 : ℤ := E11 ((M / p : ℕ) : ℤ) (W.R : ℤ) W.a W.b (ℓ : ℤ)
  let e12 : ℤ := E12 W.a W.b (ℓ : ℤ)
  let e21 : ℤ := E21 (M : ℤ) (ℓ : ℤ)
  let e22 : ℤ := E22 ((M / p : ℕ) : ℤ) (W.R : ℤ) W.a W.b (ℓ : ℤ)

  let jOf : Fin ℓ → Fin ℓ := fun t => ⟨(((c22 t : ℤ) : ZMod ℓ) * ((c21 t : ℤ) : ZMod ℓ)⁻¹).val, ZMod.val_lt _⟩
  let js : Fin ℓ := ⟨(((e22 : ℤ) : ZMod ℓ) * ((e21 : ℤ) : ZMod ℓ)⁻¹).val, ZMod.val_lt _⟩
  let πf : Option (Fin ℓ) → Option (Fin ℓ) := fun i =>
    match i with
    | none => some js
    | some t => if ((c21 t : ℤ) : ZMod ℓ) = 0 then none else some (jOf t)
  have hjOf : ∀ t, ((((jOf t : ℕ) : ℤ)) : ZMod ℓ) = ((c22 t : ℤ) : ZMod ℓ) * ((c21 t : ℤ) : ZMod ℓ)⁻¹ := by
    intro t; simp [jOf, ZMod.natCast_zmod_val]
  have hjs : ((((js : ℕ) : ℤ)) : ZMod ℓ) = ((e22 : ℤ) : ZMod ℓ) * ((e21 : ℤ) : ZMod ℓ)⁻¹ := by
    simp [js, ZMod.natCast_zmod_val]

  have hdetC : ∀ t, c11 t * c22 t - c12 t * c21 t = ℓ := fun t =>
    detC ((M / p : ℕ) : ℤ) (W.R : ℤ) (M : ℤ) W.a W.b (ℓ : ℤ) hMZ hR0 hbez _
  have hA2 : ∀ t, ((c21 t : ℤ) : ZMod ℓ) ≠ 0 → (ℓ : ℤ) ∣ c22 t - c21 t * ((jOf t : ℕ) : ℤ) := by
    intro t h
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [Int.cast_sub, Int.cast_mul, hjOf t, mul_comm, mul_assoc, inv_mul_cancel₀ h, mul_one, sub_self]
  have hA1 : ∀ t, ((c21 t : ℤ) : ZMod ℓ) ≠ 0 → (ℓ : ℤ) ∣ c12 t - c11 t * ((jOf t : ℕ) : ℤ) := by
    intro t h
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have hd : ((c11 t : ℤ) : ZMod ℓ) * ((c22 t : ℤ) : ZMod ℓ) = ((c12 t : ℤ) : ZMod ℓ) * ((c21 t : ℤ) : ZMod ℓ) := by
      have := congrArg (Int.cast : ℤ → ZMod ℓ) (hdetC t)
      push_cast at this; rw [ZMod.natCast_self] at this
      exact sub_eq_zero.mp this
    rw [Int.cast_sub, Int.cast_mul, hjOf t, ← mul_assoc, hd, mul_assoc, mul_inv_cancel₀ h, mul_one, sub_self]

  have hB0 : ∀ t, ((c21 t : ℤ) : ZMod ℓ) = 0 → (ℓ : ℤ) ∣ 1 - (W.R : ℤ) * ((t : ℕ) : ℤ) := by
    intro t h
    have h1 : (ℓ : ℤ) ∣ (M : ℤ) * (1 - (W.R : ℤ) * ((t : ℕ) : ℤ) - ℓ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
    have h2 : (ℓ : ℤ) ∣ (1 - (W.R : ℤ) * ((t : ℕ) : ℤ) - ℓ) := by
      rcases (Int.Prime.dvd_mul' hℓ h1) with h3 | h3
      · exact absurd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h3) hMl
      · exact h3
    have h3 := h2.add (dvd_refl (ℓ : ℤ))
    rwa [sub_add_cancel] at h3
  have hB1 : ∀ t, ((c21 t : ℤ) : ZMod ℓ) = 0 → (ℓ : ℤ) ∣ c11 t := by
    intro t h
    have e : c11 t = ((M / p : ℕ) : ℤ) * W.a * (1 - (W.R : ℤ) * ((t : ℕ) : ℤ)) - (W.R : ℤ) * W.b * ℓ := by
      simp only [c11, C11]; ring
    rw [e]
    exact ((hB0 t h).mul_left _).sub (dvd_mul_left _ _)
  have hB2 : ∀ t, ((c21 t : ℤ) : ZMod ℓ) = 0 → (ℓ : ℤ) ∣ c21 t := fun t h => (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

  have he21 : ((e21 : ℤ) : ZMod ℓ) ≠ 0 := by
    intro h
    have h1 : (ℓ : ℤ) ∣ (M : ℤ) * (ℓ - 1) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
    rcases (Int.Prime.dvd_mul' hℓ h1) with h3 | h3
    · exact hMl ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h3)
    · have h4 := h3.sub (dvd_refl (ℓ : ℤ))
      rw [sub_sub_cancel_left] at h4
      have h5 : (ℓ : ℤ) ∣ 1 := (dvd_neg.mp h4)
      exact hℓ.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h5)
  have hdetE : e11 * e22 - e12 * e21 = ℓ := detE ((M / p : ℕ) : ℤ) (W.R : ℤ) (M : ℤ) W.a W.b (ℓ : ℤ) hMZ hR0 hbez
  have hC2 : (ℓ : ℤ) ∣ e22 - e21 * ((js : ℕ) : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [Int.cast_sub, Int.cast_mul, hjs, mul_comm, mul_assoc, inv_mul_cancel₀ he21, mul_one, sub_self]
  have hC1 : (ℓ : ℤ) ∣ e12 - e11 * ((js : ℕ) : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have hd : ((e11 : ℤ) : ZMod ℓ) * ((e22 : ℤ) : ZMod ℓ) = ((e12 : ℤ) : ZMod ℓ) * ((e21 : ℤ) : ZMod ℓ) := by
      have := congrArg (Int.cast : ℤ → ZMod ℓ) hdetE
      push_cast at this; rw [ZMod.natCast_self] at this
      exact sub_eq_zero.mp this
    rw [Int.cast_sub, Int.cast_mul, hjs, ← mul_assoc, hd, mul_assoc, mul_inv_cancel₀ he21, mul_one, sub_self]

  have hdetA : ∀ t, ((c21 t : ℤ) : ZMod ℓ) ≠ 0 →
      (gamA ((M / p : ℕ) : ℤ) (W.R : ℤ) (M : ℤ) W.a W.b (ℓ : ℤ) ((t : ℕ) : ℤ)
        ((c12 t - c11 t * ((jOf t : ℕ) : ℤ)) / ℓ) ((c22 t - c21 t * ((jOf t : ℕ) : ℤ)) / ℓ)).det = 1 :=
    fun t h => det_gamA _ _ _ _ _ _ hMZ hR0 hℓZ0 hbez _ _ _ _ (Int.mul_ediv_cancel' (hA1 t h)) (Int.mul_ediv_cancel' (hA2 t h))
  have hdetB : ∀ t, ((c21 t : ℤ) : ZMod ℓ) = 0 →
      (gamB ((M / p : ℕ) : ℤ) (W.R : ℤ) (M : ℤ) W.a W.b (ℓ : ℤ) ((t : ℕ) : ℤ) (c11 t / ℓ) (c21 t / ℓ)).det = 1 :=
    fun t h => det_gamB _ _ _ _ _ _ hMZ hR0 hℓZ0 hbez _ _ _ (Int.mul_ediv_cancel' (hB1 t h)) (Int.mul_ediv_cancel' (hB2 t h))
      ⟨_, (Int.mul_ediv_cancel' (hB0 t h)).symm⟩
  have hdetCm : (gamC ((M / p : ℕ) : ℤ) (W.R : ℤ) (M : ℤ) W.a W.b (ℓ : ℤ) ((e12 - e11 * ((js : ℕ) : ℤ)) / ℓ)
      ((e22 - e21 * ((js : ℕ) : ℤ)) / ℓ)).det = 1 :=
    det_gamC _ _ _ _ _ _ hMZ hR0 hℓZ0 hbez _ _ _ (Int.mul_ediv_cancel' hC1) (Int.mul_ediv_cancel' hC2)
  let γA : ∀ t, ((c21 t : ℤ) : ZMod ℓ) ≠ 0 → SL(2, ℤ) := fun t h => ⟨_, hdetA t h⟩
  let γB : ∀ t, ((c21 t : ℤ) : ZMod ℓ) = 0 → SL(2, ℤ) := fun t h => ⟨_, hdetB t h⟩
  let γC : SL(2, ℤ) := ⟨_, hdetCm⟩
  obtain ⟨c', σ', hc', hσ'val, hσ'mem, hσ'GL⟩ := exists_conj W σ hσ

  have hGLA : ∀ t (h : ((c21 t : ℤ) : ZMod ℓ) ≠ 0), W.alGL * ModularForm.heckeMatrix ℓ (t : ℕ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ (γA t h) : GL (Fin 2) ℝ) * (ModularForm.heckeMatrix ℓ (jOf t : ℕ) * W.alGL) := by
    intro t h
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, val_alGL, ModularForm.val_heckeMatrix hℓ0,
      ModularForm.val_heckeMatrix hℓ0, val_mapGL]
    have e := identity_A ((M / p : ℕ) : ℤ) (W.R : ℤ) (M : ℤ) W.a W.b (ℓ : ℤ) hMZ hR0 hℓZ0 hbez ((t : ℕ) : ℤ)
      ((jOf t : ℕ) : ℤ) _ _ (Int.mul_ediv_cancel' (hA1 t h)) (Int.mul_ediv_cancel' (hA2 t h))
    push_cast at e ⊢
    exact e
  have hGLB : ∀ t (h : ((c21 t : ℤ) : ZMod ℓ) = 0), W.alGL * ModularForm.heckeMatrix ℓ (t : ℕ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ (γB t h) : GL (Fin 2) ℝ) * (ModularForm.heckeDiagMatrix ℓ * W.alGL) := by
    intro t h
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, val_alGL, ModularForm.val_heckeMatrix hℓ0,
      ModularForm.val_heckeDiagMatrix hℓ0, val_mapGL]
    have e := identity_B ((M / p : ℕ) : ℤ) (W.R : ℤ) (M : ℤ) W.a W.b (ℓ : ℤ) hMZ hR0 hℓZ0 hbez ((t : ℕ) : ℤ)
      _ _ (Int.mul_ediv_cancel' (hB1 t h)) (Int.mul_ediv_cancel' (hB2 t h))
    push_cast at e ⊢
    exact e
  have hGLC : W.alGL * ModularForm.heckeDiagMatrix ℓ =
      (Matrix.SpecialLinearGroup.mapGL ℝ γC : GL (Fin 2) ℝ) * (ModularForm.heckeMatrix ℓ (js : ℕ) * W.alGL) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, val_alGL, ModularForm.val_heckeMatrix hℓ0,
      ModularForm.val_heckeDiagMatrix hℓ0, val_mapGL]
    have e := identity_C ((M / p : ℕ) : ℤ) (W.R : ℤ) (M : ℤ) W.a W.b (ℓ : ℤ) hMZ hR0 hℓZ0 hbez ((js : ℕ) : ℤ)
      _ _ (Int.mul_ediv_cancel' hC1) (Int.mul_ediv_cancel' hC2)
    push_cast at e ⊢
    exact e

  have hmemA : ∀ t h, γA t h ∈ CongruenceSubgroup.Gamma0 M := by
    intro t h
    rw [CongruenceSubgroup.Gamma0_mem]
    show ((c21 t : ℤ) : ZMod M) = 0
    simp only [c21, C21]; push_cast; rw [ZMod.natCast_self]; ring
  have hmemB : ∀ t h, γB t h ∈ CongruenceSubgroup.Gamma0 M := by
    intro t h
    rw [CongruenceSubgroup.Gamma0_mem]
    show ((c21 t / ℓ : ℤ) : ZMod M) = 0
    have e : c21 t / ℓ = (M : ℤ) * ((1 - (W.R : ℤ) * ((t : ℕ) : ℤ) - ℓ) / ℓ) := by
      simp only [c21, C21]
      rw [Int.mul_ediv_assoc]
      exact (hB0 t h).sub (dvd_refl _)
    rw [e]; push_cast; rw [ZMod.natCast_self, zero_mul]
  have hmemC : γC ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]
    show ((e21 : ℤ) : ZMod M) = 0
    simp only [e21, E21]; push_cast; rw [ZMod.natCast_self]; ring

  have hQMz : ((M : ℤ) : ZMod (M / p)) = 0 := by
    rw [hMZ]; simp only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_one, Int.cast_zero, Int.cast_natCast, Int.cast_pow]; rw [ZMod.natCast_self, zero_mul]
  have hQM : ((M : ℕ) : ZMod (M / p)) = 0 := by exact_mod_cast hQMz
  have hQRb : (W.R : ZMod (M / p)) * (W.b : ZMod (M / p)) = -1 := by
    have := congrArg (Int.cast : ℤ → ZMod (M / p)) hbez
    simp only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_one, Int.cast_zero, Int.cast_natCast, Int.cast_pow] at this; rw [ZMod.natCast_self, zero_mul, zero_sub] at this
    linear_combination -this
  have hσQ : ((((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ)) : ZMod (M / p)) = ℓ := by
    have := congrArg (ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod (M / p))) hσℓ
    rw [map_intCast, map_natCast] at this
    exact this
  have hσ10Q : ((((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ)) : ZMod (M / p)) = 0 := by
    rw [hc']; simp only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_one, Int.cast_zero, Int.cast_natCast, Int.cast_pow]; rw [hQM, zero_mul]
  have hρ10Q : ((((ρ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ)) : ZMod (M / p)) = 0 := by
    have h1 : ((((ρ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ)) : ZMod M) = 0 := CongruenceSubgroup.Gamma0_mem.mp hρ
    have := congrArg (ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod (M / p))) h1
    rw [map_intCast, map_zero] at this
    exact this

  have hσ00 : ((((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ)) : ZMod (M / p)) * (ℓ : ZMod (M / p)) = 1 := by
    have hd := Matrix.SpecialLinearGroup.det_coe σ
    rw [Matrix.det_fin_two] at hd
    have := congrArg (Int.cast : ℤ → ZMod (M / p)) hd
    simp only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_one, Int.cast_zero, Int.cast_natCast, Int.cast_pow] at this
    rw [hσQ, hσ10Q, mul_zero, sub_zero] at this
    exact this

  have hunitA : ∀ t h, ((((γA t h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (M / p)) =
      (((ρ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (M / p)) := by
    intro t h
    show ((((c22 t - c21 t * ((jOf t : ℕ) : ℤ)) / ℓ : ℤ)) : ZMod (M / p)) = _
    set w : ℤ := (c22 t - c21 t * ((jOf t : ℕ) : ℤ)) / ℓ with hw
    have hw1 : (ℓ : ℤ) * w = c22 t - c21 t * ((jOf t : ℕ) : ℤ) := Int.mul_ediv_cancel' (hA2 t h)
    have hw2 : (ℓ : ZMod (M / p)) * (w : ZMod (M / p)) = 1 := by
      have := congrArg (Int.cast : ℤ → ZMod (M / p)) hw1
      simp only [c22, c21, C22, C21] at this
      simp only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_one, Int.cast_zero, Int.cast_natCast, Int.cast_pow] at this
      rw [hQM, ZMod.natCast_self] at this
      linear_combination this - hQRb
    linear_combination (-(w : ZMod (M / p))) * hρℓ + ((((ρ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (M / p))) * hw2
  have hunitB : ∀ t h, ((((γB t h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (M / p)) =
      ((((ρ * σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (M / p)) := by
    intro t h
    show ((c22 t : ℤ) : ZMod (M / p)) = _
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [c22, C22]
    simp only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_one, Int.cast_zero, Int.cast_natCast, Int.cast_pow]
    rw [hQM, ZMod.natCast_self, hρ10Q, hσQ, hρℓ]
    linear_combination -hQRb
  have hunitC : ((((σ' * γC : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (M / p)) =
      (((ρ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (M / p)) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hσ'val]
    show ((conjMat W _ _ c' _ 1 0 * ((e12 - e11 * ((js : ℕ) : ℤ)) / ℓ) + conjMat W _ _ c' _ 1 1 * ((e22 - e21 * ((js : ℕ) : ℤ)) / ℓ) : ℤ) : ZMod (M / p)) = _
    set w : ℤ := (e22 - e21 * ((js : ℕ) : ℤ)) / ℓ with hw
    have hw1 : (ℓ : ℤ) * w = e22 - e21 * ((js : ℕ) : ℤ) := Int.mul_ediv_cancel' hC2
    have hw2 : (ℓ : ZMod (M / p)) * ((w : ZMod (M / p)) - 1) = 0 := by
      have := congrArg (Int.cast : ℤ → ZMod (M / p)) hw1
      simp only [e22, e21, E22, E21] at this
      simp only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_one, Int.cast_zero, Int.cast_natCast, Int.cast_pow] at this
      rw [hQM, ZMod.natCast_self] at this
      linear_combination this - (ℓ : ZMod (M / p)) * hQRb
    have hw3 : (w : ZMod (M / p)) = 1 := by
      have hu : IsUnit (ℓ : ZMod (M / p)) := isUnit_iff_exists_inv.mpr ⟨_, (mul_comm _ _).trans hρℓ⟩
      have := (hu.mul_right_eq_zero).mp hw2
      exact sub_eq_zero.mp this
    simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    simp only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_one, Int.cast_zero, Int.cast_natCast, Int.cast_pow]
    rw [hw3, hQM, ZMod.natCast_self]

    have hA : -((W.b : ZMod (M / p)) * (W.R : ZMod (M / p)) * ((((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ)) : ZMod (M / p))) =
        (((ρ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (M / p)) := by
      linear_combination (-(((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod (M / p))) * hQRb +
        ((((ρ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ)) : ZMod (M / p)) * hσ00 +
        (-((((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ)) : ZMod (M / p))) * hρℓ
    linear_combination hA

  set σG : GL (Fin 2) ℝ := (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) with hσG
  set ρG : GL (Fin 2) ℝ := (Matrix.SpecialLinearGroup.mapGL ℝ ρ : GL (Fin 2) ℝ) with hρG
  have key : ∀ i, f ∣[k] (W.alGL * rep ℓ σG i) = f ∣[k] (ρG * rep ℓ σG (πf i) * W.alGL) := by
    intro i
    cases i with
    | none =>
      show f ∣[k] (W.alGL * (σG * ModularForm.heckeDiagMatrix ℓ)) = f ∣[k] (ρG * ModularForm.heckeMatrix ℓ (js : ℕ) * W.alGL)
      rw [← mul_assoc, hσG, hσ'GL, mul_assoc, hGLC, ← mul_assoc, ← map_mul,
        slash_mapGL_mul_eq hpM hHp k hf (σ' * γC) ρ (Subgroup.mul_mem _ hσ'mem hmemC) hρ hunitC, hρG, mul_assoc]
    | some t =>
      by_cases h : ((c21 t : ℤ) : ZMod ℓ) = 0
      · show f ∣[k] (W.alGL * ModularForm.heckeMatrix ℓ (t : ℕ)) =
          f ∣[k] (ρG * rep ℓ σG (if ((c21 t : ℤ) : ZMod ℓ) = 0 then none else some (jOf t)) * W.alGL)
        rw [if_pos h]
        show _ = f ∣[k] (ρG * (σG * ModularForm.heckeDiagMatrix ℓ) * W.alGL)
        rw [hGLB t h, slash_mapGL_mul_eq hpM hHp k hf (γB t h) (ρ * σ) (hmemB t h) (Subgroup.mul_mem _ hρ hσ) (hunitB t h),
          map_mul, hρG, hσG]
        simp only [mul_assoc]
      · show f ∣[k] (W.alGL * ModularForm.heckeMatrix ℓ (t : ℕ)) =
          f ∣[k] (ρG * rep ℓ σG (if ((c21 t : ℤ) : ZMod ℓ) = 0 then none else some (jOf t)) * W.alGL)
        rw [if_neg h]
        show _ = f ∣[k] (ρG * ModularForm.heckeMatrix ℓ (jOf t : ℕ) * W.alGL)
        rw [hGLA t h, slash_mapGL_mul_eq hpM hHp k hf (γA t h) ρ (hmemA t h) hρ (hunitA t h), hρG, mul_assoc]

  have finEq : ∀ t t' : Fin ℓ, ((((t : ℕ) : ℤ)) : ZMod ℓ) = ((((t' : ℕ) : ℤ)) : ZMod ℓ) → t = t' := by
    intro t t' h
    simp only [Int.cast_natCast] at h
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt ((ZMod.natCast_eq_natCast_iff _ _ _).mp h) t.2 t'.2)
  have hinjA : ∀ t t', ((c21 t : ℤ) : ZMod ℓ) ≠ 0 → ((c21 t' : ℤ) : ZMod ℓ) ≠ 0 → jOf t = jOf t' → t = t' := by
    intro t t' h h' he
    have e : ((c22 t : ℤ) : ZMod ℓ) * ((c21 t : ℤ) : ZMod ℓ)⁻¹ = ((c22 t' : ℤ) : ZMod ℓ) * ((c21 t' : ℤ) : ZMod ℓ)⁻¹ := by
      rw [← hjOf, ← hjOf, he]
    have e2 : ((c22 t : ℤ) : ZMod ℓ) * ((c21 t' : ℤ) : ZMod ℓ) = ((c22 t' : ℤ) : ZMod ℓ) * ((c21 t : ℤ) : ZMod ℓ) := by
      have := congrArg (fun w => w * ((c21 t : ℤ) : ZMod ℓ) * ((c21 t' : ℤ) : ZMod ℓ)) e
      rwa [inv_mul_cancel_right₀ h, mul_assoc, mul_comm (((c21 t : ℤ) : ZMod ℓ)), ← mul_assoc,
        inv_mul_cancel_right₀ h'] at this
    have e3 : (((c22 t * c21 t' - c22 t' * c21 t : ℤ)) : ZMod ℓ) = 0 := by
      rw [Int.cast_sub, Int.cast_mul, Int.cast_mul, e2, sub_self]
    have e4 : c22 t * c21 t' - c22 t' * c21 t =
        (M : ℤ) * ((((t : ℕ) : ℤ)) - ((t' : ℕ) : ℤ)) * ((M : ℤ) * W.a * (1 - ℓ) + (W.R : ℤ) * (((M / p : ℕ) : ℤ) * W.a * ℓ - (W.R : ℤ) * W.b)) := by
      simp only [c22, c21, C22, C21]; ring
    have e5 : (M : ℤ) * W.a * (1 - ℓ) + (W.R : ℤ) * (((M / p : ℕ) : ℤ) * W.a * ℓ - (W.R : ℤ) * W.b) =
        (W.R : ℤ) + ℓ * (W.a * (((M / p : ℕ) : ℤ) * (W.R : ℤ) - (M : ℤ))) := by
      rw [hMZ]; linear_combination (W.R : ℤ) * hbez
    rw [e4, e5, Int.cast_mul, Int.cast_mul, mul_eq_zero, mul_eq_zero] at e3
    rcases e3 with (e3 | e3) | e3
    · exact absurd e3 hMl
    · rw [Int.cast_sub, sub_eq_zero] at e3; exact finEq t t' e3
    · exfalso; apply hRl
      rw [Int.cast_add, Int.cast_mul, hll, zero_mul, add_zero] at e3
      exact e3
  have hinjB : ∀ t t', ((c21 t : ℤ) : ZMod ℓ) = 0 → ((c21 t' : ℤ) : ZMod ℓ) = 0 → t = t' := by
    intro t t' h h'
    have e3 : (((c21 t - c21 t' : ℤ)) : ZMod ℓ) = 0 := by rw [Int.cast_sub, h, h', sub_self]
    have e4 : c21 t - c21 t' = (M : ℤ) * (W.R : ℤ) * ((((t' : ℕ) : ℤ)) - ((t : ℕ) : ℤ)) := by
      simp only [c21, C21]; ring
    rw [e4, Int.cast_mul, mul_eq_zero, Int.cast_mul, mul_eq_zero] at e3
    rcases e3 with (e3 | e3) | e3
    · exact absurd e3 hMl
    · exact absurd e3 hRl
    · rw [Int.cast_sub, sub_eq_zero] at e3; exact (finEq t' t e3).symm
  have hjsne : ∀ t, ((c21 t : ℤ) : ZMod ℓ) ≠ 0 → jOf t ≠ js := by
    intro t h he
    have e : ((c22 t : ℤ) : ZMod ℓ) * ((c21 t : ℤ) : ZMod ℓ)⁻¹ = ((e22 : ℤ) : ZMod ℓ) * ((e21 : ℤ) : ZMod ℓ)⁻¹ := by
      rw [← hjOf, ← hjs, he]
    have e2 : ((c22 t : ℤ) : ZMod ℓ) * ((e21 : ℤ) : ZMod ℓ) = ((e22 : ℤ) : ZMod ℓ) * ((c21 t : ℤ) : ZMod ℓ) := by
      have := congrArg (fun w => w * ((c21 t : ℤ) : ZMod ℓ) * ((e21 : ℤ) : ZMod ℓ)) e
      rwa [inv_mul_cancel_right₀ h, mul_assoc, mul_comm (((c21 t : ℤ) : ZMod ℓ)), ← mul_assoc,
        inv_mul_cancel_right₀ he21] at this
    have e3 : (((c22 t * e21 - e22 * c21 t : ℤ)) : ZMod ℓ) = 0 := by
      rw [Int.cast_sub, Int.cast_mul, Int.cast_mul, e2, sub_self]
    have e4 : c22 t * e21 - e22 * c21 t = (M : ℤ) * (-1 + ℓ * (((M / p : ℕ) : ℤ) * (W.R : ℤ) * W.a * ((t : ℕ) : ℤ)
        - (W.R : ℤ) ^ 2 * W.b * ((t : ℕ) : ℤ) + ℓ * (((M / p : ℕ) : ℤ) * W.a - (W.R : ℤ) * W.b))) := by
      simp only [c22, c21, e21, e22, C22, C21, E21, E22]
      rw [hMZ]
      linear_combination (-(((M / p : ℕ) : ℤ) * (W.R : ℤ))) * hbez
    rw [e4, Int.cast_mul, mul_eq_zero] at e3
    rcases e3 with e3 | e3
    · exact hMl e3
    · rw [Int.cast_add, Int.cast_mul, hll, zero_mul, add_zero, Int.cast_neg, Int.cast_one, neg_eq_zero] at e3
      exact one_ne_zero e3
  have hinj : Function.Injective πf := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some t' =>
        exfalso
        change some js = (if ((c21 t' : ℤ) : ZMod ℓ) = 0 then none else some (jOf t')) at hij
        split_ifs at hij with hu
        exact hjsne t' hu (Option.some_injective _ hij).symm
    | some t =>
      cases j with
      | none =>
        exfalso
        change (if ((c21 t : ℤ) : ZMod ℓ) = 0 then none else some (jOf t)) = some js at hij
        split_ifs at hij with hu
        exact hjsne t hu (Option.some_injective _ hij)
      | some t' =>
        change (if ((c21 t : ℤ) : ZMod ℓ) = 0 then none else some (jOf t)) =
          (if ((c21 t' : ℤ) : ZMod ℓ) = 0 then none else some (jOf t')) at hij
        by_cases hu : ((c21 t : ℤ) : ZMod ℓ) = 0 <;> by_cases hu' : ((c21 t' : ℤ) : ZMod ℓ) = 0
        · rw [hinjB t t' hu hu']
        · rw [if_pos hu, if_neg hu'] at hij; exact absurd hij (by simp)
        · rw [if_neg hu, if_pos hu'] at hij; exact absurd hij (by simp)
        · rw [if_neg hu, if_neg hu'] at hij; rw [hinjA t t' hu hu' (Option.some_injective _ hij)]
  have hbij : Function.Bijective πf := Finite.injective_iff_bijective.mp hinj

  rw [ModularForm.alSlash_def, ModularForm.alSlash_def, heckeU_add_slash_eq_sum, heckeU_add_slash_eq_sum, sum_slash]
  simp only [← SlashAction.slash_mul]
  rw [← Equiv.sum_comp (Equiv.ofBijective πf hbij) (fun i => f ∣[k] (ρG * rep ℓ σG i * W.alGL))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [key i]
  rfl

end S_ModularForm_heckeU_add_slash_alSlash_eq_alSlash_heckeU_add_slash_of_not_dvd
end P2MW
export P2MW.S_ModularForm_heckeU_add_slash_alSlash_eq_alSlash_heckeU_add_slash_of_not_dvd (solution)
