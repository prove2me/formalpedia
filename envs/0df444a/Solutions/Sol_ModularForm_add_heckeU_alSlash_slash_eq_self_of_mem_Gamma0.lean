-- Prove2me | solution 1 for ModularForm.add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/5ec60b28-711e-573d-a0d8-e923315ddc07

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace WcPort

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm

noncomputable section

namespace HeckeAnalytic

def repMat (ℓ : ℕ) : Option (Fin ℓ) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(ℓ : ℤ), 0; 0, 1]
  | some j => !![1, (j : ℤ); 0, (ℓ : ℤ)]

@[scoped simp] lemma repMat_none (ℓ : ℕ) : repMat ℓ none = !![(ℓ : ℤ), 0; 0, 1] := rfl

@[scoped simp] lemma repMat_some (ℓ : ℕ) (j : Fin ℓ) : repMat ℓ (some j) = !![1, (j : ℤ); 0, (ℓ : ℤ)] :=
  rfl

lemma det_repMat (ℓ : ℕ) (i : Option (Fin ℓ)) : (repMat ℓ i).det = (ℓ : ℤ) := by
  cases i <;> simp [repMat, Matrix.det_fin_two_of]

lemma repMat_unique {ℓ : ℕ} (hℓ : 1 < ℓ) {E : Matrix (Fin 2) (Fin 2) ℤ} {m m' : Option (Fin ℓ)}
    (h : repMat ℓ m' = E * repMat ℓ m) : m' = m := by
  have hℓ' : (1 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ
  cases m with
  | none =>
    cases m' with
    | none => rfl
    | some j' =>

      exfalso
      have h00 := congrFun (congrFun h 0) 0
      simp [repMat, Matrix.mul_apply, Fin.sum_univ_two] at h00
      have hdvd : (ℓ : ℤ) ∣ 1 := ⟨E 0 0, by linarith⟩
      have := Int.le_of_dvd one_pos hdvd
      omega
  | some j =>
    cases m' with
    | none =>

      exfalso
      have h10 := congrFun (congrFun h 1) 0
      have h11 := congrFun (congrFun h 1) 1
      simp [repMat, Matrix.mul_apply, Fin.sum_univ_two] at h10 h11
      rw [← h10, zero_mul, zero_add] at h11
      have hdvd : (ℓ : ℤ) ∣ 1 := ⟨E 1 1, by linear_combination h11⟩
      have := Int.le_of_dvd one_pos hdvd
      omega
    | some j' =>

      have h00 := congrFun (congrFun h 0) 0
      have h01 := congrFun (congrFun h 0) 1
      simp [repMat, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01

      have hcast : ((j' : ℕ) : ZMod ℓ) = ((j : ℕ) : ZMod ℓ) := by
        have : ((j' : ℤ) : ZMod ℓ) = ((E 0 0 * (j : ℤ) + E 0 1 * (ℓ : ℤ) : ℤ) : ZMod ℓ) := by
          exact_mod_cast congrArg (Int.cast : ℤ → ZMod ℓ) h01
        rw [← h00] at this
        push_cast at this
        simpa using this
      have hval : (j' : ℕ) = (j : ℕ) := by
        have hj := ZMod.val_cast_of_lt j.isLt
        have hj' := ZMod.val_cast_of_lt j'.isLt
        rw [← hj, ← hj', hcast]
      exact congrArg some (Fin.ext hval)

lemma exists_cocycle {N : ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) {g : SL(2, ℤ)}
    (hg : g ∈ Gamma0 N) (i : Option (Fin ℓ)) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧ ∃ m : Option (Fin ℓ),
      repMat ℓ i * (g : Matrix (Fin 2) (Fin 2) ℤ)
        = (δ : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ m := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero

  have hdetG : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := g.det_coe
    rwa [Matrix.det_fin_two] at this
  have hNc : (N : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp hg
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set a : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  set b : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
  set c : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc
  set d : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd
  have hgmat : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := by
    rw [ha, hb, hc, hd]; exact Matrix.eta_fin_two _

  have key : ∀ p t : ℤ, ¬ (ℓ : ℤ) ∣ p → ∃ j' : Fin ℓ, (ℓ : ℤ) ∣ t - p * (j' : ℤ) := by
    intro p t hp
    have hℓpos : (0 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ.pos

    have hcop : IsCoprime (ℓ : ℤ) p :=
      (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ)).mpr hp
    obtain ⟨u, v, huv⟩ := hcop
    have hmod := Int.emod_add_mul_ediv (v * t) (ℓ : ℤ)
    have hnonneg : 0 ≤ (v * t) % (ℓ : ℤ) := Int.emod_nonneg _ hℓ0
    have hlt : (v * t) % (ℓ : ℤ) < (ℓ : ℤ) := Int.emod_lt_of_pos _ hℓpos
    have hcoe : ((((v * t) % (ℓ : ℤ)).toNat : ℕ) : ℤ) = (v * t) % (ℓ : ℤ) :=
      Int.toNat_of_nonneg hnonneg
    refine ⟨⟨((v * t) % (ℓ : ℤ)).toNat, by omega⟩,
      ⟨t * u + p * ((v * t) / (ℓ : ℤ)), ?_⟩⟩
    show t - p * ((((v * t) % (ℓ : ℤ)).toNat : ℕ) : ℤ)
      = (ℓ : ℤ) * (t * u + p * ((v * t) / (ℓ : ℤ)))
    rw [hcoe]
    linear_combination (-t) * huv + (-p) * hmod
  cases i with
  | none =>

    by_cases hcdvd : (ℓ : ℤ) ∣ c
    ·
      obtain ⟨c', hc'⟩ := hcdvd
      have hdetδ : Matrix.det !![a, (ℓ : ℤ) * b; c', d] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG + b * hc'
      refine ⟨⟨_, hdetδ⟩, ?_, none, ?_⟩
      ·
        rw [Gamma0_mem]
        show ((c' : ℤ) : ZMod N) = 0
        have hcopN : Nat.Coprime N ℓ := ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN).symm
        have hcop : IsCoprime (N : ℤ) (ℓ : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by
          simpa [Int.gcd_natCast_natCast] using hcopN)
        have hNc' : (N : ℤ) ∣ c' := by
          refine hcop.dvd_of_dvd_mul_left ?_
          rw [← hc']
          exact hNc
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
      · show repMat ℓ none * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![a, (ℓ : ℤ) * b; c', d] * repMat ℓ none
        rw [hgmat, repMat_none, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show ((ℓ : ℤ) * a + 0 * c : ℤ) = a * (ℓ : ℤ) + (ℓ : ℤ) * b * 0
          ring
        · show ((ℓ : ℤ) * b + 0 * d : ℤ) = a * 0 + (ℓ : ℤ) * b * 1
          ring
        · show (0 * a + 1 * c : ℤ) = c' * (ℓ : ℤ) + d * 0
          linear_combination hc'
        · show (0 * b + 1 * d : ℤ) = c' * 0 + d * 1
          ring
    ·
      obtain ⟨j', hj'⟩ := key c d hcdvd
      obtain ⟨e, he⟩ := hj'
      have hdetδ : Matrix.det !![(ℓ : ℤ) * a, b - a * (j' : ℤ); c, e] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG - a * he
      refine ⟨⟨_, hdetδ⟩, ?_, some j', ?_⟩
      · rw [Gamma0_mem]
        show ((c : ℤ) : ZMod N) = 0
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
      · show repMat ℓ none * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![(ℓ : ℤ) * a, b - a * (j' : ℤ); c, e] * repMat ℓ (some j')
        rw [hgmat, repMat_none, repMat_some, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show ((ℓ : ℤ) * a + 0 * c : ℤ) = (ℓ : ℤ) * a * 1 + (b - a * (j' : ℤ)) * 0
          ring
        · show ((ℓ : ℤ) * b + 0 * d : ℤ) = (ℓ : ℤ) * a * (j' : ℤ) + (b - a * (j' : ℤ)) * (ℓ : ℤ)
          ring
        · show (0 * a + 1 * c : ℤ) = c * 1 + e * 0
          ring
        · show (0 * b + 1 * d : ℤ) = c * (j' : ℤ) + e * (ℓ : ℤ)
          linear_combination he
  | some j =>

    by_cases hpdvd : (ℓ : ℤ) ∣ (a + (j : ℤ) * c)
    ·
      obtain ⟨p', hp'⟩ := hpdvd
      have hdetδ : Matrix.det !![p', b + (j : ℤ) * d; c, (ℓ : ℤ) * d] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG - d * hp'
      refine ⟨⟨_, hdetδ⟩, ?_, none, ?_⟩
      · rw [Gamma0_mem]
        show ((c : ℤ) : ZMod N) = 0
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
      · show repMat ℓ (some j) * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![p', b + (j : ℤ) * d; c, (ℓ : ℤ) * d] * repMat ℓ none
        rw [hgmat, repMat_some, repMat_none, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show (1 * a + (j : ℤ) * c : ℤ) = p' * (ℓ : ℤ) + (b + (j : ℤ) * d) * 0
          linear_combination hp'
        · show (1 * b + (j : ℤ) * d : ℤ) = p' * 0 + (b + (j : ℤ) * d) * 1
          ring
        · show (0 * a + (ℓ : ℤ) * c : ℤ) = c * (ℓ : ℤ) + (ℓ : ℤ) * d * 0
          ring
        · show (0 * b + (ℓ : ℤ) * d : ℤ) = c * 0 + (ℓ : ℤ) * d * 1
          ring
    ·
      obtain ⟨j', hj'⟩ := key (a + (j : ℤ) * c) (b + (j : ℤ) * d) hpdvd
      obtain ⟨e, he⟩ := hj'
      have hdetδ : Matrix.det
          !![a + (j : ℤ) * c, e; (ℓ : ℤ) * c, d - c * (j' : ℤ)] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG + c * he
      refine ⟨⟨_, hdetδ⟩, ?_, some j', ?_⟩
      · rw [Gamma0_mem]
        show (((ℓ : ℤ) * c : ℤ) : ZMod N) = 0
        push_cast
        rw [show ((c : ℤ) : ZMod N) = 0 from (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNc,
          mul_zero]
      · show repMat ℓ (some j) * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![a + (j : ℤ) * c, e; (ℓ : ℤ) * c, d - c * (j' : ℤ)] * repMat ℓ (some j')
        rw [hgmat, repMat_some, repMat_some, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show (1 * a + (j : ℤ) * c : ℤ) = (a + (j : ℤ) * c) * 1 + e * 0
          ring
        · show (1 * b + (j : ℤ) * d : ℤ) = (a + (j : ℤ) * c) * (j' : ℤ) + e * (ℓ : ℤ)
          linear_combination he
        · show (0 * a + (ℓ : ℤ) * c : ℤ) = (ℓ : ℤ) * c * 1 + (d - c * (j' : ℤ)) * 0
          ring
        · show (0 * b + (ℓ : ℤ) * d : ℤ) = (ℓ : ℤ) * c * (j' : ℤ) + (d - c * (j' : ℤ)) * (ℓ : ℤ)
          ring

def repGL (ℓ : ℕ) [NeZero ℓ] (i : Option (Fin ℓ)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((repMat ℓ i).map (algebraMap ℤ ℝ)) (by
    have h : ((repMat ℓ i).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) (repMat ℓ i).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, det_repMat]
    simp [NeZero.ne ℓ])

@[scoped simp] lemma repGL_coe (ℓ : ℕ) [NeZero ℓ] (i : Option (Fin ℓ)) :
    (repGL ℓ i : Matrix (Fin 2) (Fin 2) ℝ) = (repMat ℓ i).map (algebraMap ℤ ℝ) := rfl

private lemma mapGL_coe' (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

private lemma map_int_mul (M P : Matrix (Fin 2) (Fin 2) ℤ) :
    (M * P).map (algebraMap ℤ ℝ) = M.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

def heckeSlashSum (k : ℤ) (ℓ : ℕ) [NeZero ℓ] (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ i : Option (Fin ℓ), f ∣[k] repGL ℓ i

lemma heckeSlashSum_add (k : ℤ) (ℓ : ℕ) [NeZero ℓ] (f g : ℍ → ℂ) :
    heckeSlashSum k ℓ (f + g) = heckeSlashSum k ℓ f + heckeSlashSum k ℓ g := by
  simp only [heckeSlashSum, SlashAction.add_slash]
  exact Finset.sum_add_distrib

theorem heckeSlashSum_slash {N : ℕ} {k : ℤ} {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    {γ : GL (Fin 2) ℝ}
    (hγ : γ ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    (heckeSlashSum k ℓ f) ∣[k] γ = heckeSlashSum k ℓ f := by

  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ

  choose δ hδ m hm using exists_cocycle hℓ hℓN hg

  have hinj : Function.Injective m := by
    intro i₁ i₂ him
    have h₁ := hm i₁
    have h₂ := hm i₂
    rw [him] at h₁

    have hg_inv : (g : Matrix (Fin 2) (Fin 2) ℤ) * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hδ₂ : (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        ((δ i₂ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hcomb : repMat ℓ i₁ =
        ((δ i₁ * (δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ i₂ := by
      have step : repMat ℓ i₁ * (g : Matrix (Fin 2) (Fin 2) ℤ) =
          (((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
            (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
            (repMat ℓ i₂ * (g : Matrix (Fin 2) (Fin 2) ℤ)) := by
        calc repMat ℓ i₁ * (g : Matrix (Fin 2) (Fin 2) ℤ)
            = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ (m i₂) := h₁
          _ = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                ((((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                  (((δ i₂ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ (m i₂))) := by
              rw [← mul_assoc (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), hδ₂, one_mul]
          _ = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                ((((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                  (repMat ℓ i₂ * (g : Matrix (Fin 2) (Fin 2) ℤ))) := by rw [h₂]
          _ = (((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
                (repMat ℓ i₂ * (g : Matrix (Fin 2) (Fin 2) ℤ)) := by
              simp only [mul_assoc]
      have := congrArg (· * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) step
      simp only [mul_assoc, hg_inv, mul_one] at this
      rw [this, Matrix.SpecialLinearGroup.coe_mul, mul_assoc]
    exact repMat_unique hℓ.one_lt hcomb
  have hbij : Function.Bijective m := Finite.injective_iff_bijective.mp hinj

  have hmGL : ∀ i, repGL ℓ i * Matrix.SpecialLinearGroup.mapGL ℝ g =
      Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * repGL ℓ (m i) := by
    intro i
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    show (repGL ℓ i : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((Matrix.SpecialLinearGroup.mapGL ℝ (δ i) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        (repGL ℓ (m i) : Matrix (Fin 2) (Fin 2) ℝ)
    rw [repGL_coe, repGL_coe, mapGL_coe', mapGL_coe', ← map_int_mul, ← map_int_mul, hm i]

  calc (heckeSlashSum k ℓ f) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g)
      = ∑ i : Option (Fin ℓ), (f ∣[k] repGL ℓ i) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g) := by
        rw [heckeSlashSum, SlashAction.sum_slash]
    _ = ∑ i : Option (Fin ℓ), f ∣[k] (repGL ℓ i * Matrix.SpecialLinearGroup.mapGL ℝ g) := by
        simp_rw [SlashAction.slash_mul]
    _ = ∑ i : Option (Fin ℓ),
          f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * repGL ℓ (m i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hmGL i]
    _ = ∑ i : Option (Fin ℓ),
          (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ (δ i)) ∣[k] repGL ℓ (m i) := by
        simp_rw [SlashAction.slash_mul]
    _ = ∑ i : Option (Fin ℓ), f ∣[k] repGL ℓ (m i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hf (Matrix.SpecialLinearGroup.mapGL ℝ (δ i)) (Subgroup.mem_map.mpr ⟨δ i, hδ i, rfl⟩)]
    _ = ∑ i : Option (Fin ℓ), f ∣[k] repGL ℓ i := hbij.sum_comp fun i => f ∣[k] repGL ℓ i
    _ = heckeSlashSum k ℓ f := rfl

end HeckeAnalytic
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic"

namespace SlashInvariantForm

open HeckeAnalytic CongruenceSubgroup

variable {N : ℕ} {k : ℤ}

def hecke (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : SlashInvariantForm (Gamma0 N) k) : SlashInvariantForm (Gamma0 N) k :=
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  { toFun := heckeSlashSum k ℓ f
    slash_action_eq' := fun _ hγ => heckeSlashSum_slash hℓ hℓN f.slash_action_eq' hγ }

end SlashInvariantForm
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic"

namespace HeckeAnalytic

open OnePoint
open scoped Manifold

def repGLQ (ℓ : ℕ) [NeZero ℓ] (i : Option (Fin ℓ)) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((repMat ℓ i).map (algebraMap ℤ ℚ)) (by
    have h : ((repMat ℓ i).map (algebraMap ℤ ℚ)).det = (algebraMap ℤ ℚ) (repMat ℓ i).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, det_repMat]
    simp [NeZero.ne ℓ])

@[scoped simp] lemma repGLQ_coe (ℓ : ℕ) [NeZero ℓ] (i : Option (Fin ℓ)) :
    (repGLQ ℓ i : Matrix (Fin 2) (Fin 2) ℚ) = (repMat ℓ i).map (algebraMap ℤ ℚ) := rfl

lemma repGLQ_map_castHom (ℓ : ℕ) [NeZero ℓ] (i : Option (Fin ℓ)) :
    (repGLQ ℓ i).map (Rat.castHom ℝ) = repGL ℓ i := by
  apply Units.ext
  show (Rat.castHom ℝ).mapMatrix ((repGLQ ℓ i : Matrix (Fin 2) (Fin 2) ℚ))
      = (repGL ℓ i : Matrix (Fin 2) (Fin 2) ℝ)
  rw [repGLQ_coe, repGL_coe, RingHom.mapMatrix_apply, Matrix.map_map]
  congr 1

lemma isCusp_smul_of_rat {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) {g : GL (Fin 2) ℝ}
    (gQ : GL (Fin 2) ℚ) (hg : gQ.map (Rat.castHom ℝ) = g) : IsCusp (g • c) 𝒮ℒ := by
  subst hg
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  refine ⟨gQ • c₀, ?_⟩
  rw [← Rat.coe_castHom, OnePoint.map_smul]

lemma isCusp_repGL_smul {N : ℕ} [NeZero N] {ℓ : ℕ} [NeZero ℓ] (i : Option (Fin ℓ))
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsCusp (repGL ℓ i • c) ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  exact isCusp_smul_of_rat hc (repGLQ ℓ i) (repGLQ_map_castHom ℓ i)

private lemma isBoundedAt_zero {c : OnePoint ℝ} {k : ℤ} :
    IsBoundedAt c (0 : ℍ → ℂ) k := fun _ _ => by
  rw [SlashAction.zero_slash]
  exact (Filter.zero_zeroAtFilter _).boundedAtFilter

private lemma isZeroAt_zero {c : OnePoint ℝ} {k : ℤ} :
    IsZeroAt c (0 : ℍ → ℂ) k := fun _ _ => by
  rw [SlashAction.zero_slash]
  exact Filter.zero_zeroAtFilter _

private lemma isBoundedAt_finsetSum {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ}
    {c : OnePoint ℝ} {k : ℤ} (h : ∀ i ∈ s, IsBoundedAt c (F i) k) :
    IsBoundedAt c (∑ i ∈ s, F i) k := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using isBoundedAt_zero
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact (h a (Finset.mem_cons_self ..)).add (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

private lemma isZeroAt_finsetSum {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ}
    {c : OnePoint ℝ} {k : ℤ} (h : ∀ i ∈ s, IsZeroAt c (F i) k) :
    IsZeroAt c (∑ i ∈ s, F i) k := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using isZeroAt_zero
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact (h a (Finset.mem_cons_self ..)).add (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

lemma heckeSlashSum_mdiff {k : ℤ} {ℓ : ℕ} [NeZero ℓ] {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (heckeSlashSum k ℓ f) := by
  show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (∑ i : Option (Fin ℓ), f ∣[k] repGL ℓ i)
  exact MDifferentiable.sum fun i _ => hf.slash k (repGL ℓ i)

lemma heckeSlashSum_isBoundedAt {N : ℕ} [NeZero N] {k : ℤ} {ℓ : ℕ} [NeZero ℓ] {f : ℍ → ℂ}
    (hf : ∀ c' : OnePoint ℝ,
      IsCusp c' ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) →
      IsBoundedAt c' f k)
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsBoundedAt c (heckeSlashSum k ℓ f) k := by
  show IsBoundedAt c (∑ i : Option (Fin ℓ), f ∣[k] repGL ℓ i) k
  refine isBoundedAt_finsetSum _ fun i _ => ?_
  exact IsBoundedAt.smul_iff.mp (hf _ (isCusp_repGL_smul (N := N) i hc))

lemma heckeSlashSum_isZeroAt {N : ℕ} [NeZero N] {k : ℤ} {ℓ : ℕ} [NeZero ℓ] {f : ℍ → ℂ}
    (hf : ∀ c' : OnePoint ℝ,
      IsCusp c' ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) →
      IsZeroAt c' f k)
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsZeroAt c (heckeSlashSum k ℓ f) k := by
  show IsZeroAt c (∑ i : Option (Fin ℓ), f ∣[k] repGL ℓ i) k
  refine isZeroAt_finsetSum _ fun i _ => ?_
  exact IsZeroAt.smul_iff.mp (hf _ (isCusp_repGL_smul (N := N) i hc))

end HeckeAnalytic
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic"

namespace ModularForm

open HeckeAnalytic CongruenceSubgroup OnePoint

variable {N : ℕ} [NeZero N] {k : ℤ}

private def _root_.WcPort.ModularForm.hecke (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : ModularForm (Gamma0 N) k) :
    ModularForm (Gamma0 N) k :=
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  { toSlashInvariantForm := SlashInvariantForm.hecke ℓ hℓ hℓN f.toSlashInvariantForm
    holo' := heckeSlashSum_mdiff f.holo'
    bdd_at_cusps' := fun hc =>
      heckeSlashSum_isBoundedAt (fun _ hc' => f.bdd_at_cusps' hc') hc }

p2m_export "WcPort.ModularForm" "hecke"
end ModularForm
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic"

namespace CuspForm

open HeckeAnalytic CongruenceSubgroup OnePoint

variable {N : ℕ} [NeZero N] {k : ℤ}

private def _root_.WcPort.CuspForm.hecke (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : CuspForm (Gamma0 N) k) :
    CuspForm (Gamma0 N) k :=
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  { toSlashInvariantForm := SlashInvariantForm.hecke ℓ hℓ hℓN f.toSlashInvariantForm
    holo' := heckeSlashSum_mdiff f.holo'
    zero_at_cusps' := fun hc =>
      heckeSlashSum_isZeroAt (fun _ hc' => f.zero_at_cusps' hc') hc }

p2m_export "WcPort.CuspForm" "hecke"
end CuspForm
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic"

end
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic"

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped MatrixGroups ModularForm Real

noncomputable section

namespace HeckeAnalytic

variable {ℓ : ℕ} [NeZero ℓ]

lemma repGL_entry (i : Option (Fin ℓ)) (a b : Fin 2) :
    (repGL ℓ i) a b = algebraMap ℤ ℝ ((repMat ℓ i) a b) := by
  show ((repGL ℓ i : Matrix (Fin 2) (Fin 2) ℝ)) a b = _
  rw [repGL_coe, Matrix.map_apply]

lemma val_det_repGL (i : Option (Fin ℓ)) : ((repGL ℓ i).det : ℝ) = (ℓ : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, repGL_coe]
  have h : ((repMat ℓ i).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) (repMat ℓ i).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [h, det_repMat]
  simp

lemma det_repGL_pos (i : Option (Fin ℓ)) : 0 < ((repGL ℓ i).det : ℝ) := by
  rw [val_det_repGL]
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)

lemma denom_repGL_some (j : Fin ℓ) (z : ℂ) : denom (repGL ℓ (some j)) z = (ℓ : ℂ) := by
  simp [UpperHalfPlane.denom, repGL_entry, repMat]

lemma denom_repGL_none (z : ℂ) : denom (repGL ℓ none) z = 1 := by
  simp [UpperHalfPlane.denom, repGL_entry, repMat]

lemma num_repGL_some (j : Fin ℓ) (z : ℂ) : num (repGL ℓ (some j)) z = z + (j : ℕ) := by
  simp [UpperHalfPlane.num, repGL_entry, repMat]

lemma num_repGL_none (z : ℂ) : num (repGL ℓ none) z = (ℓ : ℂ) * z := by
  simp [UpperHalfPlane.num, repGL_entry, repMat]

lemma coe_smul_repGL_some (j : Fin ℓ) (τ : ℍ) :
    ((repGL ℓ (some j) • τ : ℍ) : ℂ) = ((τ : ℂ) + (j : ℕ)) / (ℓ : ℂ) := by
  rw [coe_smul_of_det_pos (det_repGL_pos _), num_repGL_some, denom_repGL_some]

lemma coe_smul_repGL_none (τ : ℍ) :
    ((repGL ℓ none • τ : ℍ) : ℂ) = (ℓ : ℂ) * τ := by
  rw [coe_smul_of_det_pos (det_repGL_pos _), num_repGL_none, denom_repGL_none, div_one]

lemma σ_repGL_apply (i : Option (Fin ℓ)) (z : ℂ) : σ (repGL ℓ i) z = z := by
  rw [UpperHalfPlane.σ, if_pos (det_repGL_pos i)]
  simp

lemma slash_repGL_some_apply (k : ℤ) (f : ℍ → ℂ) (j : Fin ℓ) (τ : ℍ) :
    (f ∣[k] repGL ℓ (some j)) τ = (ℓ : ℂ)⁻¹ * f (repGL ℓ (some j) • τ) := by
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne ℓ)
  rw [ModularForm.slash_apply, σ_repGL_apply, val_det_repGL, denom_repGL_some,
    abs_of_pos hℓR]
  push_cast
  have hexp : (k - 1) + (-k) = (-1 : ℤ) := by ring
  rw [mul_assoc, ← zpow_add₀ hℓC, hexp, _root_.zpow_neg_one]
  ring

lemma slash_repGL_none_apply (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] repGL ℓ none) τ = (ℓ : ℂ) ^ (k - 1) * f (repGL ℓ none • τ) := by
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
  rw [ModularForm.slash_apply, σ_repGL_apply, val_det_repGL, denom_repGL_none,
    abs_of_pos hℓR, _root_.one_zpow, mul_one]
  push_cast
  ring

local notation "𝕢" => Function.Periodic.qParam

lemma qParam_one_eq (z : ℂ) : 𝕢 1 z = Complex.exp (2 * π * Complex.I * z) := by
  simp [Function.Periodic.qParam]

lemma qParam_eq (h : ℝ) (z : ℂ) : 𝕢 h z = Complex.exp (2 * π * Complex.I * z / h) := rfl

lemma qParam_one_smul_none (τ : ℍ) :
    𝕢 1 ((repGL ℓ none • τ : ℍ) : ℂ) = (𝕢 1 (τ : ℂ)) ^ ℓ := by
  rw [coe_smul_repGL_none, qParam_one_eq, qParam_one_eq, ← Complex.exp_nat_mul]
  congr 1
  ring

lemma qParam_one_smul_some (j : Fin ℓ) (τ : ℍ) :
    𝕢 1 ((repGL ℓ (some j) • τ : ℍ) : ℂ)
      = Complex.exp (2 * π * Complex.I * (j : ℕ) / ℓ) * 𝕢 (ℓ : ℝ) (τ : ℂ) := by
  rw [coe_smul_repGL_some, qParam_one_eq, qParam_eq, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma qParam_pow_period (τ : ℍ) : (𝕢 (ℓ : ℝ) (τ : ℂ)) ^ ℓ = 𝕢 1 (τ : ℂ) := by
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne ℓ)
  rw [qParam_eq, qParam_one_eq, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

end HeckeAnalytic
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic"

end
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic"

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace HeckeAnalytic

lemma exists_cocycle_U {N : ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) {g : SL(2, ℤ)}
    (hg : g ∈ Gamma0 N) (j : Fin ℓ) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧ ∃ j' : Fin ℓ,
      repMat ℓ (some j) * (g : Matrix (Fin 2) (Fin 2) ℤ)
        = (δ : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ (some j') := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero

  have hdetG : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := g.det_coe
    rwa [Matrix.det_fin_two] at this
  have hNc : (N : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp hg
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set a : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  set b : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
  set c : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc
  set d : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd
  have hgmat : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := by
    rw [ha, hb, hc, hd]; exact Matrix.eta_fin_two _

  have hℓc : (ℓ : ℤ) ∣ c := dvd_trans (by exact_mod_cast hℓN) hNc

  have hpdvd : ¬ (ℓ : ℤ) ∣ (a + (j : ℤ) * c) := by
    intro hdvd
    have hjc : (ℓ : ℤ) ∣ (j : ℤ) * c := hℓc.mul_left _
    have hla : (ℓ : ℤ) ∣ a := by
      have h3 := dvd_sub hdvd hjc
      have h4 : a + (j : ℤ) * c - (j : ℤ) * c = a := by ring
      rwa [h4] at h3
    have h1 : (ℓ : ℤ) ∣ 1 := by
      have h5 : (ℓ : ℤ) ∣ a * d - b * c := dvd_sub (hla.mul_right d) (hℓc.mul_left b)
      rwa [hdetG] at h5
    have h6 := Int.le_of_dvd one_pos h1
    have hℓ1 : (1 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ.one_lt
    omega

  have key : ∀ p t : ℤ, ¬ (ℓ : ℤ) ∣ p → ∃ j' : Fin ℓ, (ℓ : ℤ) ∣ t - p * (j' : ℤ) := by
    intro p t hp
    have hℓpos : (0 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ.pos
    have hcop : IsCoprime (ℓ : ℤ) p :=
      (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ)).mpr hp
    obtain ⟨u, v, huv⟩ := hcop
    have hmod := Int.emod_add_mul_ediv (v * t) (ℓ : ℤ)
    have hnonneg : 0 ≤ (v * t) % (ℓ : ℤ) := Int.emod_nonneg _ hℓ0
    have hlt : (v * t) % (ℓ : ℤ) < (ℓ : ℤ) := Int.emod_lt_of_pos _ hℓpos
    have hcoe : ((((v * t) % (ℓ : ℤ)).toNat : ℕ) : ℤ) = (v * t) % (ℓ : ℤ) :=
      Int.toNat_of_nonneg hnonneg
    refine ⟨⟨((v * t) % (ℓ : ℤ)).toNat, by omega⟩,
      ⟨t * u + p * ((v * t) / (ℓ : ℤ)), ?_⟩⟩
    show t - p * ((((v * t) % (ℓ : ℤ)).toNat : ℕ) : ℤ)
      = (ℓ : ℤ) * (t * u + p * ((v * t) / (ℓ : ℤ)))
    rw [hcoe]
    linear_combination (-t) * huv + (-p) * hmod
  obtain ⟨j', hj'⟩ := key (a + (j : ℤ) * c) (b + (j : ℤ) * d) hpdvd
  obtain ⟨e, he⟩ := hj'
  have hdetδ : Matrix.det
      !![a + (j : ℤ) * c, e; (ℓ : ℤ) * c, d - c * (j' : ℤ)] = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdetG + c * he
  refine ⟨⟨_, hdetδ⟩, ?_, j', ?_⟩
  ·
    rw [Gamma0_mem]
    show (((ℓ : ℤ) * c : ℤ) : ZMod N) = 0
    push_cast
    rw [show ((c : ℤ) : ZMod N) = 0 from (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNc,
      mul_zero]
  · show repMat ℓ (some j) * (g : Matrix (Fin 2) (Fin 2) ℤ)
      = !![a + (j : ℤ) * c, e; (ℓ : ℤ) * c, d - c * (j' : ℤ)] * repMat ℓ (some j')
    rw [hgmat, repMat_some, repMat_some, Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun x y => ?_
    fin_cases x <;> fin_cases y
    · show (1 * a + (j : ℤ) * c : ℤ) = (a + (j : ℤ) * c) * 1 + e * 0
      ring
    · show (1 * b + (j : ℤ) * d : ℤ) = (a + (j : ℤ) * c) * (j' : ℤ) + e * (ℓ : ℤ)
      linear_combination he
    · show (0 * a + (ℓ : ℤ) * c : ℤ) = (ℓ : ℤ) * c * 1 + (d - c * (j' : ℤ)) * 0
      ring
    · show (0 * b + (ℓ : ℤ) * d : ℤ) = (ℓ : ℤ) * c * (j' : ℤ) + (d - c * (j' : ℤ)) * (ℓ : ℤ)
      ring

def heckeUSlashSum (k : ℤ) (ℓ : ℕ) [NeZero ℓ] (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ j : Fin ℓ, f ∣[k] repGL ℓ (some j)

lemma heckeUSlashSum_add (k : ℤ) (ℓ : ℕ) [NeZero ℓ] (f g : ℍ → ℂ) :
    heckeUSlashSum k ℓ (f + g) = heckeUSlashSum k ℓ f + heckeUSlashSum k ℓ g := by
  simp only [heckeUSlashSum, SlashAction.add_slash]
  exact Finset.sum_add_distrib

lemma heckeUSlashSum_smul (k : ℤ) (ℓ : ℕ) [NeZero ℓ] (c : ℂ) (f : ℍ → ℂ) :
    heckeUSlashSum k ℓ (c • f) = c • heckeUSlashSum k ℓ f := by

  simp only [heckeUSlashSum, ModularForm.smul_slash, σ_repGL_apply]
  rw [Finset.smul_sum]

private lemma mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

private lemma map_int_mul_eq (M P : Matrix (Fin 2) (Fin 2) ℤ) :
    (M * P).map (algebraMap ℤ ℝ) = M.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

theorem heckeUSlashSum_slash {N : ℕ} {k : ℤ} {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    {γ : GL (Fin 2) ℝ}
    (hγ : γ ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    (heckeUSlashSum k ℓ f) ∣[k] γ = heckeUSlashSum k ℓ f := by

  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ

  choose δ hδ m hm using exists_cocycle_U hℓ hℓN hg

  have hinj : Function.Injective m := by
    intro i₁ i₂ him
    have h₁ := hm i₁
    have h₂ := hm i₂
    rw [him] at h₁
    have hg_inv : (g : Matrix (Fin 2) (Fin 2) ℤ) * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hδ₂ : (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        ((δ i₂ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hcomb : repMat ℓ (some i₁) =
        ((δ i₁ * (δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ (some i₂) := by
      have step : repMat ℓ (some i₁) * (g : Matrix (Fin 2) (Fin 2) ℤ) =
          (((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
            (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
            (repMat ℓ (some i₂) * (g : Matrix (Fin 2) (Fin 2) ℤ)) := by
        calc repMat ℓ (some i₁) * (g : Matrix (Fin 2) (Fin 2) ℤ)
            = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ (some (m i₂)) := h₁
          _ = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                ((((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                  (((δ i₂ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                    repMat ℓ (some (m i₂)))) := by
              rw [← mul_assoc (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), hδ₂, one_mul]
          _ = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                ((((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                  (repMat ℓ (some i₂) * (g : Matrix (Fin 2) (Fin 2) ℤ))) := by rw [h₂]
          _ = (((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
                (repMat ℓ (some i₂) * (g : Matrix (Fin 2) (Fin 2) ℤ)) := by
              simp only [mul_assoc]
      have := congrArg (· * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) step
      simp only [mul_assoc, hg_inv, mul_one] at this
      rw [this, Matrix.SpecialLinearGroup.coe_mul, mul_assoc]
    exact Option.some_injective _ (repMat_unique hℓ.one_lt hcomb)
  have hbij : Function.Bijective m := Finite.injective_iff_bijective.mp hinj

  have hmGL : ∀ i, repGL ℓ (some i) * Matrix.SpecialLinearGroup.mapGL ℝ g =
      Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * repGL ℓ (some (m i)) := by
    intro i
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    show (repGL ℓ (some i) : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((Matrix.SpecialLinearGroup.mapGL ℝ (δ i) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        (repGL ℓ (some (m i)) : Matrix (Fin 2) (Fin 2) ℝ)
    rw [repGL_coe, repGL_coe, mapGL_coe_eq, mapGL_coe_eq, ← map_int_mul_eq, ← map_int_mul_eq,
      hm i]

  calc (heckeUSlashSum k ℓ f) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g)
      = ∑ i : Fin ℓ, (f ∣[k] repGL ℓ (some i)) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g) := by
        rw [heckeUSlashSum, SlashAction.sum_slash]
    _ = ∑ i : Fin ℓ, f ∣[k] (repGL ℓ (some i) * Matrix.SpecialLinearGroup.mapGL ℝ g) := by
        simp_rw [SlashAction.slash_mul]
    _ = ∑ i : Fin ℓ,
          f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * repGL ℓ (some (m i))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hmGL i]
    _ = ∑ i : Fin ℓ,
          (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ (δ i)) ∣[k] repGL ℓ (some (m i)) := by
        simp_rw [SlashAction.slash_mul]
    _ = ∑ i : Fin ℓ, f ∣[k] repGL ℓ (some (m i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hf (Matrix.SpecialLinearGroup.mapGL ℝ (δ i)) (Subgroup.mem_map.mpr ⟨δ i, hδ i, rfl⟩)]
    _ = ∑ i : Fin ℓ, f ∣[k] repGL ℓ (some i) :=
        hbij.sum_comp fun i => f ∣[k] repGL ℓ (some i)
    _ = heckeUSlashSum k ℓ f := rfl

open OnePoint

lemma heckeUSlashSum_mdiff {k : ℤ} {ℓ : ℕ} [NeZero ℓ] {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (heckeUSlashSum k ℓ f) := by
  show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (∑ j : Fin ℓ, f ∣[k] repGL ℓ (Option.some j))
  exact MDifferentiable.sum fun i _ => hf.slash k (repGL ℓ (Option.some i))

lemma heckeUSlashSum_isBoundedAt {N : ℕ} [NeZero N] {k : ℤ} {ℓ : ℕ} [NeZero ℓ] {f : ℍ → ℂ}
    (hf : ∀ c' : OnePoint ℝ,
      IsCusp c' ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) →
      IsBoundedAt c' f k)
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsBoundedAt c (heckeUSlashSum k ℓ f) k := by
  show IsBoundedAt c (∑ j : Fin ℓ, f ∣[k] repGL ℓ (Option.some j)) k
  refine isBoundedAt_finsetSum _ fun i _ => ?_
  exact IsBoundedAt.smul_iff.mp (hf _ (isCusp_repGL_smul (N := N) (Option.some i) hc))

lemma heckeUSlashSum_isZeroAt {N : ℕ} [NeZero N] {k : ℤ} {ℓ : ℕ} [NeZero ℓ] {f : ℍ → ℂ}
    (hf : ∀ c' : OnePoint ℝ,
      IsCusp c' ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) →
      IsZeroAt c' f k)
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsZeroAt c (heckeUSlashSum k ℓ f) k := by
  show IsZeroAt c (∑ j : Fin ℓ, f ∣[k] repGL ℓ (Option.some j)) k
  refine isZeroAt_finsetSum _ fun i _ => ?_
  exact IsZeroAt.smul_iff.mp (hf _ (isCusp_repGL_smul (N := N) (Option.some i) hc))

end HeckeAnalytic
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic"

namespace SlashInvariantForm

open HeckeAnalytic CongruenceSubgroup

variable {N : ℕ} {k : ℤ}

private def _root_.WcPort.SlashInvariantForm.heckeU (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    (f : SlashInvariantForm (Gamma0 N) k) : SlashInvariantForm (Gamma0 N) k :=
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  { toFun := heckeUSlashSum k ℓ f
    slash_action_eq' := fun _ hγ => heckeUSlashSum_slash hℓ hℓN f.slash_action_eq' hγ }

p2m_export "WcPort.SlashInvariantForm" "heckeU"
end SlashInvariantForm
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic"

namespace ModularForm

open HeckeAnalytic CongruenceSubgroup OnePoint

variable {N : ℕ} [NeZero N] {k : ℤ}

private def _root_.WcPort.ModularForm.heckeU (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (f : ModularForm (Gamma0 N) k) :
    ModularForm (Gamma0 N) k :=
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  { toSlashInvariantForm := SlashInvariantForm.heckeU ℓ hℓ hℓN f.toSlashInvariantForm
    holo' := heckeUSlashSum_mdiff f.holo'
    bdd_at_cusps' := fun hc =>
      heckeUSlashSum_isBoundedAt (fun _ hc' => f.bdd_at_cusps' hc') hc }

p2m_export "WcPort.ModularForm" "heckeU"
lemma heckeU_coe (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    (f : ModularForm (Gamma0 N) k) :
    ⇑(ModularForm.heckeU ℓ hℓ hℓN f) = heckeUSlashSum k ℓ (⇑f) := rfl

lemma heckeU_add (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (f g : ModularForm (Gamma0 N) k) :
    ModularForm.heckeU ℓ hℓ hℓN (f + g)
      = ModularForm.heckeU ℓ hℓ hℓN f + ModularForm.heckeU ℓ hℓ hℓN g := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  ext τ
  simp only [heckeU_coe, ModularForm.coe_add, Pi.add_apply, heckeUSlashSum_add]

lemma heckeU_smul (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (c : ℂ)
    (f : ModularForm (Gamma0 N) k) :
    ModularForm.heckeU ℓ hℓ hℓN (c • f) = c • ModularForm.heckeU ℓ hℓ hℓN f := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  ext τ

  show heckeUSlashSum k ℓ (c • ⇑f) τ = c • heckeUSlashSum k ℓ (⇑f) τ
  rw [heckeUSlashSum_smul]
  rfl

def heckeUHom (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) :
    ModularForm (Gamma0 N) k →ₗ[ℂ] ModularForm (Gamma0 N) k where
  toFun := ModularForm.heckeU ℓ hℓ hℓN
  map_add' := heckeU_add ℓ hℓ hℓN
  map_smul' := heckeU_smul ℓ hℓ hℓN

@[scoped simp] lemma heckeUHom_apply (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    (f : ModularForm (Gamma0 N) k) :
    heckeUHom ℓ hℓ hℓN f = ModularForm.heckeU ℓ hℓ hℓN f := rfl

end ModularForm
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm"

namespace CuspForm

open HeckeAnalytic CongruenceSubgroup OnePoint

variable {N : ℕ} [NeZero N] {k : ℤ}

private def _root_.WcPort.CuspForm.heckeU (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (f : CuspForm (Gamma0 N) k) :
    CuspForm (Gamma0 N) k :=
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  { toSlashInvariantForm := SlashInvariantForm.heckeU ℓ hℓ hℓN f.toSlashInvariantForm
    holo' := heckeUSlashSum_mdiff f.holo'
    zero_at_cusps' := fun hc =>
      heckeUSlashSum_isZeroAt (fun _ hc' => f.zero_at_cusps' hc') hc }

p2m_export "WcPort.CuspForm" "heckeU"
lemma heckeU_coe (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    (f : CuspForm (Gamma0 N) k) :
    ⇑(CuspForm.heckeU ℓ hℓ hℓN f) = heckeUSlashSum k ℓ (⇑f) := rfl

lemma heckeU_add (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (f g : CuspForm (Gamma0 N) k) :
    CuspForm.heckeU ℓ hℓ hℓN (f + g)
      = CuspForm.heckeU ℓ hℓ hℓN f + CuspForm.heckeU ℓ hℓ hℓN g := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  ext τ
  simp only [heckeU_coe, CuspForm.coe_add, Pi.add_apply, heckeUSlashSum_add]

lemma heckeU_smul (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (c : ℂ) (f : CuspForm (Gamma0 N) k) :
    CuspForm.heckeU ℓ hℓ hℓN (c • f) = c • CuspForm.heckeU ℓ hℓ hℓN f := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  ext τ
  show heckeUSlashSum k ℓ (c • ⇑f) τ = c • heckeUSlashSum k ℓ (⇑f) τ
  rw [heckeUSlashSum_smul]
  rfl

def heckeUHom (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) :
    CuspForm (Gamma0 N) k →ₗ[ℂ] CuspForm (Gamma0 N) k where
  toFun := CuspForm.heckeU ℓ hℓ hℓN
  map_add' := heckeU_add ℓ hℓ hℓN
  map_smul' := heckeU_smul ℓ hℓ hℓN

@[scoped simp] lemma heckeUHom_apply (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (f : CuspForm (Gamma0 N) k) :
    heckeUHom ℓ hℓ hℓN f = CuspForm.heckeU ℓ hℓ hℓN f := rfl

end CuspForm
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm"

end
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm"

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace ModularCurve

variable (M q : ℕ)

structure ALData : Type where

  R : ℕ

  hM : M = q * R

  a : ℤ

  b : ℤ

  bezout : (q : ℤ) * a - (R : ℤ) * b = 1

namespace ALData

variable {M q : ℕ} (W : ALData M q)

lemma hM_int : (M : ℤ) = (q : ℤ) * (W.R : ℤ) := by exact_mod_cast W.hM

include W in

lemma q_pos [NeZero M] : 0 < q := by
  rcases Nat.eq_zero_or_pos q with h | h
  · exact absurd (W.hM.trans (Nat.mul_eq_zero.mpr (Or.inl h))) (NeZero.ne M)
  · exact h

include W in

lemma R_pos [NeZero M] : 0 < W.R := by
  rcases Nat.eq_zero_or_pos W.R with h | h
  · exact absurd (W.hM.trans (Nat.mul_eq_zero.mpr (Or.inr h))) (NeZero.ne M)
  · exact h

def mat : Matrix (Fin 2) (Fin 2) ℤ := !![(q : ℤ) * W.a, W.b; (q : ℤ) * (W.R : ℤ), (q : ℤ)]

@[scoped simp] lemma det_mat : W.mat.det = (q : ℤ) := by
  rw [mat, Matrix.det_fin_two_of]
  linear_combination (q : ℤ) * W.bezout

lemma mat_lowerLeft : W.mat 1 0 = (M : ℤ) := by
  rw [mat, W.hM_int]
  simp

theorem mat_mul_normalizes (α β c δ : ℤ)
    (hdet : α * δ - β * ((q : ℤ) * (W.R : ℤ) * c) = 1) :
    ∃ p r s t : ℤ, p * t - r * ((q : ℤ) * (W.R : ℤ) * s) = 1 ∧
      W.mat * !![α, β; (q : ℤ) * (W.R : ℤ) * c, δ]
        = !![p, r; (q : ℤ) * (W.R : ℤ) * s, t] * W.mat := by

  refine ⟨(q : ℤ) * W.a * α + W.b * ((q : ℤ) * (W.R : ℤ)) * c
        - (W.R : ℤ) * ((q : ℤ) * W.a * β + W.b * δ),
      -(W.a * α * W.b) - W.b ^ 2 * (W.R : ℤ) * c + (q : ℤ) * W.a ^ 2 * β + W.a * W.b * δ,
      α + (q : ℤ) * c - (W.R : ℤ) * β - δ,
      -((W.R : ℤ) * W.b) * (α + (q : ℤ) * c) + W.a * ((q : ℤ) * (W.R : ℤ) * β + (q : ℤ) * δ),
      ?_, ?_⟩
  ·
    linear_combination ((q : ℤ) * W.a - (W.R : ℤ) * W.b) ^ 2 * hdet
      + ((q : ℤ) * W.a - (W.R : ℤ) * W.b + 1) * W.bezout
  ·
    rw [mat, Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · show (q : ℤ) * W.a * α + W.b * ((q : ℤ) * (W.R : ℤ) * c)
        = ((q : ℤ) * W.a * α + W.b * ((q : ℤ) * (W.R : ℤ)) * c
            - (W.R : ℤ) * ((q : ℤ) * W.a * β + W.b * δ)) * ((q : ℤ) * W.a)
          + (-(W.a * α * W.b) - W.b ^ 2 * (W.R : ℤ) * c + (q : ℤ) * W.a ^ 2 * β
              + W.a * W.b * δ) * ((q : ℤ) * (W.R : ℤ))
      linear_combination
        (-((W.R : ℤ) * W.b * c * (q : ℤ) + W.a * α * (q : ℤ))) * W.bezout
    · show (q : ℤ) * W.a * β + W.b * δ
        = ((q : ℤ) * W.a * α + W.b * ((q : ℤ) * (W.R : ℤ)) * c
            - (W.R : ℤ) * ((q : ℤ) * W.a * β + W.b * δ)) * W.b
          + (-(W.a * α * W.b) - W.b ^ 2 * (W.R : ℤ) * c + (q : ℤ) * W.a ^ 2 * β
              + W.a * W.b * δ) * (q : ℤ)
      linear_combination (-(W.a * β * (q : ℤ) + W.b * δ)) * W.bezout
    · show (q : ℤ) * (W.R : ℤ) * α + (q : ℤ) * ((q : ℤ) * (W.R : ℤ) * c)
        = (q : ℤ) * (W.R : ℤ) * (α + (q : ℤ) * c - (W.R : ℤ) * β - δ) * ((q : ℤ) * W.a)
          + (-((W.R : ℤ) * W.b) * (α + (q : ℤ) * c)
              + W.a * ((q : ℤ) * (W.R : ℤ) * β + (q : ℤ) * δ)) * ((q : ℤ) * (W.R : ℤ))
      linear_combination
        (-((W.R : ℤ) * α * (q : ℤ) + (W.R : ℤ) * c * (q : ℤ) ^ 2)) * W.bezout
    · show (q : ℤ) * (W.R : ℤ) * β + (q : ℤ) * δ
        = (q : ℤ) * (W.R : ℤ) * (α + (q : ℤ) * c - (W.R : ℤ) * β - δ) * W.b
          + (-((W.R : ℤ) * W.b) * (α + (q : ℤ) * c)
              + W.a * ((q : ℤ) * (W.R : ℤ) * β + (q : ℤ) * δ)) * (q : ℤ)
      linear_combination (-((W.R : ℤ) * β * (q : ℤ) + δ * (q : ℤ))) * W.bezout

def sqUnit : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(q : ℤ) * W.a ^ 2 + (W.R : ℤ) * W.b, W.b * (W.a + 1);
     (q : ℤ) * (W.R : ℤ) * (W.a + 1), (W.R : ℤ) * W.b + (q : ℤ)]

theorem mat_sq : W.mat * W.mat = (q : ℤ) • W.sqUnit := by
  rw [mat, sqUnit, Matrix.mul_fin_two]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · show (q : ℤ) * W.a * ((q : ℤ) * W.a) + W.b * ((q : ℤ) * (W.R : ℤ))
      = (q : ℤ) * ((q : ℤ) * W.a ^ 2 + (W.R : ℤ) * W.b)
    ring
  · show (q : ℤ) * W.a * W.b + W.b * (q : ℤ) = (q : ℤ) * (W.b * (W.a + 1))
    ring
  · show (q : ℤ) * (W.R : ℤ) * ((q : ℤ) * W.a) + (q : ℤ) * ((q : ℤ) * (W.R : ℤ))
      = (q : ℤ) * ((q : ℤ) * (W.R : ℤ) * (W.a + 1))
    ring
  · show (q : ℤ) * (W.R : ℤ) * W.b + (q : ℤ) * (q : ℤ)
      = (q : ℤ) * ((W.R : ℤ) * W.b + (q : ℤ))
    ring

@[scoped simp] lemma det_sqUnit : W.sqUnit.det = 1 := by
  rw [sqUnit, Matrix.det_fin_two_of]
  linear_combination ((q : ℤ) * W.a - (W.R : ℤ) * W.b + 1) * W.bezout

def sqUnitSL : SL(2, ℤ) := ⟨W.sqUnit, W.det_sqUnit⟩

@[scoped simp] lemma sqUnitSL_coe : (W.sqUnitSL : Matrix (Fin 2) (Fin 2) ℤ) = W.sqUnit := rfl

lemma sqUnitSL_mem : W.sqUnitSL ∈ Gamma0 M := by
  rw [Gamma0_mem]
  show (((W.sqUnit 1 0 : ℤ) : ZMod M) = 0)
  have h : W.sqUnit 1 0 = (M : ℤ) * (W.a + 1) := by
    rw [sqUnit, W.hM_int]; simp
  rw [h]
  push_cast
  simp

theorem nonempty_of_prime_of_dvd_of_not_sq_dvd (hq : q.Prime) (hqM : q ∣ M)
    (hsq : ¬ q ^ 2 ∣ M) : Nonempty (ALData M q) := by
  obtain ⟨R, hR⟩ := hqM

  have hqR : ¬ q ∣ R := by
    rintro ⟨t, rfl⟩
    exact hsq ⟨t, by rw [hR]; ring⟩

  have hqR' : ¬ (q : ℤ) ∣ (R : ℤ) := by exact_mod_cast hqR
  have hcop : IsCoprime (q : ℤ) (R : ℤ) :=
    (Nat.prime_iff_prime_int.mp hq).coprime_iff_not_dvd.mpr hqR'
  obtain ⟨u, v, huv⟩ := hcop
  exact ⟨⟨R, hR, u, -v, by linear_combination huv⟩⟩

theorem isEmpty_four_two : IsEmpty (ALData 4 2) := by
  constructor
  rintro ⟨R, hM, a, b, hbez⟩

  have hR : R = 2 := by omega
  subst hR

  omega

end ALData
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData"

end ModularCurve
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve"

namespace HeckeAnalytic

open ModularCurve OnePoint

variable {M q : ℕ} (W : ALData M q)

private def _root_.WcPort.HeckeAnalytic.alGL [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (W.mat.map (algebraMap ℤ ℝ)) (by
    have h : ((W.mat).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) W.mat.det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, W.det_mat]
    simpa using W.q_pos.ne')

p2m_export "WcPort.HeckeAnalytic" "alGL"
@[scoped simp] lemma alGL_coe [NeZero M] :
    (alGL W : Matrix (Fin 2) (Fin 2) ℝ) = (W.mat).map (algebraMap ℤ ℝ) := rfl

lemma alGL_entry [NeZero M] (i j : Fin 2) :
    (alGL W) i j = algebraMap ℤ ℝ (W.mat i j) := by
  show ((alGL W : Matrix (Fin 2) (Fin 2) ℝ)) i j = _
  rw [alGL_coe, Matrix.map_apply]

lemma val_det_alGL [NeZero M] : ((alGL W).det : ℝ) = (q : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, alGL_coe]
  have h : ((W.mat).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) W.mat.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [h, W.det_mat]
  simp

lemma det_alGL_pos [NeZero M] : 0 < ((alGL W).det : ℝ) := by
  rw [val_det_alGL]
  exact_mod_cast W.q_pos

lemma σ_alGL_apply [NeZero M] (z : ℂ) : σ (alGL W) z = z := by
  rw [UpperHalfPlane.σ, if_pos (det_alGL_pos W)]
  simp

def alGLQ [NeZero M] : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (W.mat.map (algebraMap ℤ ℚ)) (by
    have h : ((W.mat).map (algebraMap ℤ ℚ)).det = (algebraMap ℤ ℚ) W.mat.det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, W.det_mat]
    simpa using W.q_pos.ne')

lemma alGLQ_map_castHom [NeZero M] : (alGLQ W).map (Rat.castHom ℝ) = alGL W := by
  apply Units.ext
  show (Rat.castHom ℝ).mapMatrix ((alGLQ W : Matrix (Fin 2) (Fin 2) ℚ))
      = (alGL W : Matrix (Fin 2) (Fin 2) ℝ)
  show (Rat.castHom ℝ).mapMatrix ((W.mat).map (algebraMap ℤ ℚ))
      = (W.mat).map (algebraMap ℤ ℝ)
  rw [RingHom.mapMatrix_apply, Matrix.map_map]
  congr 1

lemma isCusp_alGL_smul [NeZero M] {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsCusp (alGL W • c) ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  exact isCusp_smul_of_rat hc (alGLQ W) (alGLQ_map_castHom W)

private def _root_.WcPort.HeckeAnalytic.alSlash (k : ℤ) [NeZero M] (f : ℍ → ℂ) : ℍ → ℂ := f ∣[k] alGL W

p2m_export "WcPort.HeckeAnalytic" "alSlash"
lemma alSlash_add (k : ℤ) [NeZero M] (f g : ℍ → ℂ) :
    alSlash W k (f + g) = alSlash W k f + alSlash W k g := by
  simp only [alSlash, SlashAction.add_slash]

lemma alSlash_smul (k : ℤ) [NeZero M] (c : ℂ) (f : ℍ → ℂ) :
    alSlash W k (c • f) = c • alSlash W k f := by
  simp only [alSlash, ModularForm.smul_slash, σ_alGL_apply]

lemma exists_cocycle_al [NeZero M] {g : SL(2, ℤ)} (hg : g ∈ Gamma0 M) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 M ∧
      alGL W * Matrix.SpecialLinearGroup.mapGL ℝ g
        = Matrix.SpecialLinearGroup.mapGL ℝ δ * alGL W := by

  have hdetG : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := g.det_coe
    rwa [Matrix.det_fin_two] at this
  have hMc : (M : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp hg
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set α : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with hα
  set β : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hβ
  set γlo : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hγlo
  set δen : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hδen
  obtain ⟨c, hc⟩ := hMc

  have hgmat : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![α, β; (q : ℤ) * (W.R : ℤ) * c, δen] := by
    rw [← W.hM_int, ← hc, hα, hβ, hγlo, hδen]
    exact Matrix.eta_fin_two _

  have hdet' : α * δen - β * ((q : ℤ) * (W.R : ℤ) * c) = 1 := by
    rw [← W.hM_int, ← hc]; linear_combination hdetG
  obtain ⟨p, r, s, t, hdet1, hmat⟩ := W.mat_mul_normalizes α β c δen hdet'

  have hdetδ : Matrix.det !![p, r; (q : ℤ) * (W.R : ℤ) * s, t] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet1
  refine ⟨⟨_, hdetδ⟩, ?_, ?_⟩
  ·
    rw [Gamma0_mem]
    show ((((q : ℤ) * (W.R : ℤ) * s : ℤ)) : ZMod M) = 0
    rw [← W.hM_int]
    push_cast
    simp
  ·
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    show (alGL W : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = ((Matrix.SpecialLinearGroup.mapGL ℝ (⟨_, hdetδ⟩ : SL(2, ℤ)) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) * (alGL W : Matrix (Fin 2) (Fin 2) ℝ)
    rw [alGL_coe, mapGL_coe_eq, mapGL_coe_eq, ← map_int_mul_eq, ← map_int_mul_eq]
    congr 1
    rw [hgmat]
    exact hmat

theorem alSlash_slash {k : ℤ} [NeZero M] {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    {γ : GL (Fin 2) ℝ}
    (hγ : γ ∈ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    (alSlash W k f) ∣[k] γ = alSlash W k f := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
  obtain ⟨δ, hδ, hcocycle⟩ := exists_cocycle_al W hg
  calc (f ∣[k] alGL W) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g)
      = f ∣[k] (alGL W * Matrix.SpecialLinearGroup.mapGL ℝ g) := by
        rw [SlashAction.slash_mul]
    _ = f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ δ * alGL W) := by rw [hcocycle]
    _ = (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ δ) ∣[k] alGL W := by
        rw [SlashAction.slash_mul]
    _ = f ∣[k] alGL W := by
        rw [hf (Matrix.SpecialLinearGroup.mapGL ℝ δ) (Subgroup.mem_map.mpr ⟨δ, hδ, rfl⟩)]

lemma alSlash_mdiff {k : ℤ} [NeZero M] {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (alSlash W k f) :=
  hf.slash k (alGL W)

lemma alSlash_isBoundedAt {k : ℤ} [NeZero M] {f : ℍ → ℂ}
    (hf : ∀ c' : OnePoint ℝ,
      IsCusp c' ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) →
      IsBoundedAt c' f k)
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsBoundedAt c (alSlash W k f) k :=
  IsBoundedAt.smul_iff.mp (hf _ (isCusp_alGL_smul W hc))

lemma alSlash_isZeroAt {k : ℤ} [NeZero M] {f : ℍ → ℂ}
    (hf : ∀ c' : OnePoint ℝ,
      IsCusp c' ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) →
      IsZeroAt c' f k)
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsZeroAt c (alSlash W k f) k :=
  IsZeroAt.smul_iff.mp (hf _ (isCusp_alGL_smul W hc))

variable (q) in

def scalarGL (hq : 0 < q) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℝ), 0; 0, (q : ℝ)] (by
    rw [Matrix.det_fin_two_of]
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    simpa using mul_ne_zero hq' hq')

@[scoped simp] lemma scalarGL_coe (hq : 0 < q) :
    (scalarGL q hq : Matrix (Fin 2) (Fin 2) ℝ) = !![(q : ℝ), 0; 0, (q : ℝ)] := rfl

private lemma val_det_scalarGL (hq : 0 < q) : ((scalarGL q hq).det : ℝ) = (q : ℝ) ^ 2 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, scalarGL_coe, Matrix.det_fin_two_of]
  ring

private lemma denom_scalarGL (hq : 0 < q) (z : ℂ) : denom (scalarGL q hq) z = (q : ℝ) := by
  simp [UpperHalfPlane.denom, scalarGL_coe]

private lemma num_scalarGL (hq : 0 < q) (z : ℂ) : num (scalarGL q hq) z = (q : ℝ) * z := by
  simp [UpperHalfPlane.num, scalarGL_coe]

private lemma det_scalarGL_pos (hq : 0 < q) : 0 < ((scalarGL q hq).det : ℝ) := by
  rw [val_det_scalarGL]
  have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  positivity

private lemma scalarGL_smul (hq : 0 < q) (τ : ℍ) : scalarGL q hq • τ = τ := by
  have hqC : ((q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by exact_mod_cast hq.ne' : ((q : ℝ)) ≠ 0)
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_scalarGL_pos hq), num_scalarGL, denom_scalarGL,
    mul_comm, mul_div_assoc, div_self hqC, mul_one]

private lemma slash_scalarGL (k : ℤ) (hq : 0 < q) (f : ℍ → ℂ) :
    f ∣[k] scalarGL q hq = ((q : ℂ) ^ (k - 2)) • f := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  ext τ
  rw [ModularForm.slash_apply, Pi.smul_apply, smul_eq_mul]
  have hσ : σ (scalarGL q hq) (f (scalarGL q hq • τ)) = f (scalarGL q hq • τ) := by
    rw [UpperHalfPlane.σ, if_pos (det_scalarGL_pos hq)]
    rfl
  rw [hσ, scalarGL_smul, val_det_scalarGL, denom_scalarGL,
    abs_of_pos (by positivity : (0 : ℝ) < (q : ℝ) ^ 2)]

  have h1 : (((q : ℝ) ^ 2 : ℝ) : ℂ) = (q : ℂ) ^ (2 : ℕ) := by push_cast; ring
  have h2 : (((q : ℝ) : ℝ) : ℂ) = (q : ℂ) := by push_cast; ring
  rw [h1, h2, ← _root_.zpow_natCast ((q : ℂ)) 2, ← _root_.zpow_mul, mul_assoc, ← zpow_add₀ hqC]
  rw [show (2 : ℕ) * (k - 1) + -k = k - 2 by push_cast; ring]
  ring

private lemma alGL_mul_alGL [NeZero M] :
    alGL W * alGL W = scalarGL q W.q_pos * Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (alGL W : Matrix (Fin 2) (Fin 2) ℝ) * (alGL W : Matrix (Fin 2) (Fin 2) ℝ)
      = (scalarGL q W.q_pos : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ)
  rw [alGL_coe, scalarGL_coe, mapGL_coe_eq, ALData.sqUnitSL_coe, ← map_int_mul_eq, W.mat_sq]

  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.natCast_apply]

theorem alSlash_alSlash (k : ℤ) [NeZero M] {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) :
    alSlash W k (alSlash W k f) = ((q : ℂ) ^ (k - 2)) • f := by

  have hfu : f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL) = f :=
    hf _ (Subgroup.mem_map.mpr ⟨W.sqUnitSL, W.sqUnitSL_mem, rfl⟩)
  calc alSlash W k (alSlash W k f)
      = f ∣[k] (alGL W * alGL W) := by
        rw [alSlash, alSlash, SlashAction.slash_mul]
    _ = (f ∣[k] scalarGL q W.q_pos) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL) := by
        rw [alGL_mul_alGL, SlashAction.slash_mul]
    _ = (((q : ℂ) ^ (k - 2)) • f) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL) := by
        rw [slash_scalarGL]
    _ = ((q : ℂ) ^ (k - 2)) • (f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL)) := by
        rw [ModularForm.smul_slash]
        congr 1
        rw [UpperHalfPlane.σ, if_pos]
        · rfl
        · simp
    _ = ((q : ℂ) ^ (k - 2)) • f := by rw [hfu]

theorem alSlash_alSlash_two [NeZero M] {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      f ∣[(2 : ℤ)] γ = f) :
    alSlash W 2 (alSlash W 2 f) = f := by
  rw [alSlash_alSlash W 2 hf]
  norm_num

end HeckeAnalytic
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve"

namespace SlashInvariantForm

open HeckeAnalytic ModularCurve CongruenceSubgroup

variable {M q : ℕ} {k : ℤ}

def atkinLehner [NeZero M] (W : ALData M q) (f : SlashInvariantForm (Gamma0 M) k) :
    SlashInvariantForm (Gamma0 M) k where
  toFun := alSlash W k f
  slash_action_eq' := fun _ hγ => alSlash_slash W f.slash_action_eq' hγ

@[scoped simp] lemma atkinLehner_coe [NeZero M] (W : ALData M q)
    (f : SlashInvariantForm (Gamma0 M) k) :
    ⇑(atkinLehner W f) = alSlash W k f := rfl

end SlashInvariantForm
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm"

namespace ModularForm

open HeckeAnalytic ModularCurve CongruenceSubgroup OnePoint

variable {M q : ℕ} {k : ℤ}

private def _root_.WcPort.ModularForm.atkinLehner [NeZero M] (W : ALData M q) (f : ModularForm (Gamma0 M) k) :
    ModularForm (Gamma0 M) k where
  toSlashInvariantForm := SlashInvariantForm.atkinLehner W f.toSlashInvariantForm
  holo' := alSlash_mdiff W f.holo'
  bdd_at_cusps' := fun hc => alSlash_isBoundedAt W (fun _ hc' => f.bdd_at_cusps' hc') hc

p2m_export "WcPort.ModularForm" "atkinLehner"
@[scoped simp] lemma atkinLehner_coe [NeZero M] (W : ALData M q) (f : ModularForm (Gamma0 M) k) :
    ⇑(atkinLehner W f) = alSlash W k f := rfl

lemma atkinLehner_add [NeZero M] (W : ALData M q) (f g : ModularForm (Gamma0 M) k) :
    atkinLehner W (f + g) = atkinLehner W f + atkinLehner W g := by
  ext τ
  show alSlash W k (⇑f + ⇑g) τ = (alSlash W k ⇑f + alSlash W k ⇑g) τ
  rw [HeckeAnalytic.alSlash_add]

lemma atkinLehner_smul [NeZero M] (W : ALData M q) (c : ℂ) (f : ModularForm (Gamma0 M) k) :
    atkinLehner W (c • f) = c • atkinLehner W f := by
  ext τ
  show alSlash W k (c • ⇑f) τ = (c • alSlash W k ⇑f) τ
  rw [HeckeAnalytic.alSlash_smul]

def atkinLehnerHom [NeZero M] (W : ALData M q) :
    ModularForm (Gamma0 M) k →ₗ[ℂ] ModularForm (Gamma0 M) k where
  toFun := atkinLehner W
  map_add' := atkinLehner_add W
  map_smul' := atkinLehner_smul W

end ModularForm
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm"

namespace CuspForm

open HeckeAnalytic ModularCurve CongruenceSubgroup OnePoint

variable {M q : ℕ} {k : ℤ}

private def _root_.WcPort.CuspForm.atkinLehner [NeZero M] (W : ALData M q) (f : CuspForm (Gamma0 M) k) :
    CuspForm (Gamma0 M) k where
  toSlashInvariantForm := SlashInvariantForm.atkinLehner W f.toSlashInvariantForm
  holo' := alSlash_mdiff W f.holo'
  zero_at_cusps' := fun hc => alSlash_isZeroAt W (fun _ hc' => f.zero_at_cusps' hc') hc

p2m_export "WcPort.CuspForm" "atkinLehner"
@[scoped simp] lemma atkinLehner_coe [NeZero M] (W : ALData M q) (f : CuspForm (Gamma0 M) k) :
    ⇑(atkinLehner W f) = alSlash W k f := rfl

lemma atkinLehner_add [NeZero M] (W : ALData M q) (f g : CuspForm (Gamma0 M) k) :
    atkinLehner W (f + g) = atkinLehner W f + atkinLehner W g := by
  ext τ
  show alSlash W k (⇑f + ⇑g) τ = (alSlash W k ⇑f + alSlash W k ⇑g) τ
  rw [HeckeAnalytic.alSlash_add]

lemma atkinLehner_smul [NeZero M] (W : ALData M q) (c : ℂ) (f : CuspForm (Gamma0 M) k) :
    atkinLehner W (c • f) = c • atkinLehner W f := by
  ext τ
  show alSlash W k (c • ⇑f) τ = (c • alSlash W k ⇑f) τ
  rw [HeckeAnalytic.alSlash_smul]

def atkinLehnerHom [NeZero M] (W : ALData M q) :
    CuspForm (Gamma0 M) k →ₗ[ℂ] CuspForm (Gamma0 M) k where
  toFun := atkinLehner W
  map_add' := atkinLehner_add W
  map_smul' := atkinLehner_smul W

@[scoped simp] lemma atkinLehnerHom_apply [NeZero M] (W : ALData M q) (f : CuspForm (Gamma0 M) k) :
    atkinLehnerHom W f = atkinLehner W f := rfl

theorem atkinLehner_atkinLehner_eq_smul [NeZero M] (W : ALData M q)
    (f : CuspForm (Gamma0 M) k) :
    atkinLehner W (atkinLehner W f) = ((q : ℂ) ^ (k - 2)) • f := by
  ext τ
  exact congrFun (alSlash_alSlash W k f.slash_action_eq') τ

theorem atkinLehner_atkinLehner [NeZero M] (W : ALData M q) (f : CuspForm (Gamma0 M) 2) :
    atkinLehner W (atkinLehner W f) = f := by
  rw [atkinLehner_atkinLehner_eq_smul]
  norm_num

theorem sq_eq_one_of_atkinLehner_eq_smul [NeZero M] (W : ALData M q)
    {f : CuspForm (Gamma0 M) 2} (hf : f ≠ 0) {lam : ℂ}
    (hlam : atkinLehner W f = lam • f) : lam ^ 2 = 1 := by

  have h1 : atkinLehner W (atkinLehner W f) = (lam ^ 2) • f := by
    rw [hlam, atkinLehner_smul, hlam, smul_smul, pow_two]
  rw [atkinLehner_atkinLehner] at h1

  by_contra hne
  have h2 : (lam ^ 2 - 1) • f = 0 := by
    rw [sub_smul, one_smul, ← h1, sub_self]
  have hne' : lam ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hne
  refine hf ?_
  calc f = (lam ^ 2 - 1)⁻¹ • ((lam ^ 2 - 1) • f) := by
        rw [smul_smul, inv_mul_cancel₀ hne', one_smul]
    _ = 0 := by rw [h2, smul_zero]

end CuspForm
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm"

end
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm"

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace ModularCurve
namespace ALData

variable {M q : ℕ} (W : ALData M q)

def traceRepMat : Option (Fin q) → Matrix (Fin 2) (Fin 2) ℤ
  | none => W.mat
  | some j => HeckeAnalytic.repMat q (some j)

@[scoped simp] lemma traceRepMat_none : W.traceRepMat none = W.mat := rfl

@[scoped simp] lemma traceRepMat_some (j : Fin q) :
    W.traceRepMat (some j) = !![1, (j : ℤ); 0, (q : ℤ)] := rfl

lemma det_traceRepMat (i : Option (Fin q)) : (W.traceRepMat i).det = (q : ℤ) := by
  cases i with
  | none => exact W.det_mat
  | some j => exact HeckeAnalytic.det_repMat q (some j)

lemma not_dvd_b (hq : 1 < q) : ¬ (q : ℤ) ∣ W.b := by
  intro hdvd
  have h1 : (q : ℤ) ∣ 1 := by
    have h2 : (q : ℤ) ∣ (q : ℤ) * W.a - (W.R : ℤ) * W.b :=
      dvd_sub (Dvd.intro _ rfl) (hdvd.mul_left _)
    rwa [W.bezout] at h2
  have := Int.le_of_dvd one_pos h1
  omega

lemma not_dvd_R (hq : 1 < q) : ¬ (q : ℤ) ∣ (W.R : ℤ) := by
  intro hdvd
  have h1 : (q : ℤ) ∣ 1 := by
    have h2 : (q : ℤ) ∣ (q : ℤ) * W.a - (W.R : ℤ) * W.b :=
      dvd_sub (Dvd.intro _ rfl) (hdvd.mul_right _)
    rwa [W.bezout] at h2
  have := Int.le_of_dvd one_pos h1
  omega

lemma traceRepMat_unique (hq : 1 < q) {E : Matrix (Fin 2) (Fin 2) ℤ}
    {i i' : Option (Fin q)} (h : W.traceRepMat i' = E * W.traceRepMat i) : i' = i := by
  cases i with
  | none =>
    cases i' with
    | none => rfl
    | some j' =>

      exfalso
      rw [traceRepMat_some, traceRepMat_none, ALData.mat, Matrix.eta_fin_two E,
        Matrix.mul_fin_two] at h
      have h00 : (1 : ℤ) = E 0 0 * ((q : ℤ) * W.a) + E 0 1 * ((q : ℤ) * (W.R : ℤ)) :=
        congrFun (congrFun h 0) 0
      have hdvd : (q : ℤ) ∣ 1 :=
        ⟨E 0 0 * W.a + E 0 1 * (W.R : ℤ), by linear_combination h00⟩
      have := Int.le_of_dvd one_pos hdvd
      omega
  | some j =>
    cases i' with
    | none =>

      exfalso
      rw [traceRepMat_some, traceRepMat_none, ALData.mat, Matrix.eta_fin_two E,
        Matrix.mul_fin_two] at h
      have h00 : (q : ℤ) * W.a = E 0 0 * 1 + E 0 1 * 0 := congrFun (congrFun h 0) 0
      have h01 : W.b = E 0 0 * (j : ℤ) + E 0 1 * (q : ℤ) := congrFun (congrFun h 0) 1
      exact W.not_dvd_b hq ⟨W.a * (j : ℤ) + E 0 1, by linear_combination h01 - (j : ℤ) * h00⟩
    | some j' =>
      exact HeckeAnalytic.repMat_unique hq h

lemma exists_fin_dvd_sub_mul (hq : q.Prime) {p : ℤ} (t : ℤ) (hp : ¬ (q : ℤ) ∣ p) :
    ∃ j' : Fin q, (q : ℤ) ∣ t - p * (j' : ℤ) := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hqpos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq.pos
  have hcop : IsCoprime (q : ℤ) p :=
    (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hq)).mpr hp
  obtain ⟨u, v, huv⟩ := hcop
  have hmod := Int.emod_add_mul_ediv (v * t) (q : ℤ)
  have hnonneg : 0 ≤ (v * t) % (q : ℤ) := Int.emod_nonneg _ hq0
  have hlt : (v * t) % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos _ hqpos
  have hcoe : ((((v * t) % (q : ℤ)).toNat : ℕ) : ℤ) = (v * t) % (q : ℤ) :=
    Int.toNat_of_nonneg hnonneg
  refine ⟨⟨((v * t) % (q : ℤ)).toNat, by omega⟩,
    ⟨t * u + p * ((v * t) / (q : ℤ)), ?_⟩⟩
  show t - p * ((((v * t) % (q : ℤ)).toNat : ℕ) : ℤ) = (q : ℤ) * (t * u + p * ((v * t) / (q : ℤ)))
  rw [hcoe]
  linear_combination (-t) * huv + (-p) * hmod

theorem exists_traceRep_cocycle (hq : q.Prime) {g : SL(2, ℤ)}
    (hg : g ∈ Gamma0 W.R) (i : Option (Fin q)) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 M ∧ ∃ i' : Option (Fin q),
      W.traceRepMat i * (g : Matrix (Fin 2) (Fin 2) ℤ)
        = (δ : Matrix (Fin 2) (Fin 2) ℤ) * W.traceRepMat i' := by
  have hq1 : 1 < q := hq.one_lt

  have hdetG : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := g.det_coe
    rwa [Matrix.det_fin_two] at this
  have hRc : (W.R : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp hg
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set α : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with hα
  set β : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hβ
  set d : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd
  obtain ⟨c, hc⟩ := hRc
  have hgmat : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![α, β; (W.R : ℤ) * c, d] := by
    rw [← hc, hα, hβ, hd]
    exact Matrix.eta_fin_two _
  have hdet' : α * d - β * ((W.R : ℤ) * c) = 1 := by
    rw [← hc]; linear_combination hdetG

  have hmemM : ∀ x : ℤ, (((q : ℤ) * (W.R : ℤ) * x : ℤ) : ZMod M) = 0 := by
    intro x
    rw [← W.hM_int]
    push_cast
    simp
  cases i with
  | none =>

    by_cases hqc : (q : ℤ) ∣ c
    ·
      obtain ⟨c', rfl⟩ := hqc
      obtain ⟨p, r, s, t, hdet1, hmat⟩ := W.mat_mul_normalizes α β c' d
        (by linear_combination hdet')
      have hdetδ : Matrix.det !![p, r; (q : ℤ) * (W.R : ℤ) * s, t] = 1 := by
        rw [Matrix.det_fin_two_of]; linear_combination hdet1
      refine ⟨⟨_, hdetδ⟩, ?_, none, ?_⟩
      · rw [Gamma0_mem]; exact hmemM s
      · rw [traceRepMat_none, hgmat,
          show (W.R : ℤ) * ((q : ℤ) * c') = (q : ℤ) * (W.R : ℤ) * c' by ring]
        exact hmat
    ·

      have hqRc : ¬ (q : ℤ) ∣ (W.R : ℤ) * c :=
        fun hdvd => hqc ((Int.Prime.dvd_mul' hq hdvd).resolve_left (W.not_dvd_R hq1))
      obtain ⟨j', hj'⟩ := exists_fin_dvd_sub_mul hq d hqRc
      obtain ⟨e, he⟩ := hj'

      have hdetδ : Matrix.det
          !![(W.R : ℤ) * W.b * c + (q : ℤ) * W.a * α, -(W.a * α * (j' : ℤ)) + W.a * β + W.b * e;
             (q : ℤ) * (W.R : ℤ) * (α + c), -((W.R : ℤ) * α * (j' : ℤ)) + (W.R : ℤ) * β
               + (q : ℤ) * e] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination ((q : ℤ) * W.a - (W.R : ℤ) * W.b) * hdet' + W.bezout
          + ((W.R : ℤ) * α * W.b - W.a * α * (q : ℤ)) * he
      refine ⟨⟨_, hdetδ⟩, ?_, some j', ?_⟩
      · rw [Gamma0_mem]; exact hmemM (α + c)
      · rw [traceRepMat_none, traceRepMat_some, hgmat]
        show W.mat * _ = _
        rw [ALData.mat, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show (q : ℤ) * W.a * α + W.b * ((W.R : ℤ) * c)
            = ((W.R : ℤ) * W.b * c + (q : ℤ) * W.a * α) * 1
              + (-(W.a * α * (j' : ℤ)) + W.a * β + W.b * e) * 0
          ring
        · show (q : ℤ) * W.a * β + W.b * d
            = ((W.R : ℤ) * W.b * c + (q : ℤ) * W.a * α) * (j' : ℤ)
              + (-(W.a * α * (j' : ℤ)) + W.a * β + W.b * e) * (q : ℤ)
          linear_combination W.b * he
        · show (q : ℤ) * (W.R : ℤ) * α + (q : ℤ) * ((W.R : ℤ) * c)
            = (q : ℤ) * (W.R : ℤ) * (α + c) * 1
              + (-((W.R : ℤ) * α * (j' : ℤ)) + (W.R : ℤ) * β + (q : ℤ) * e) * 0
          ring
        · show (q : ℤ) * (W.R : ℤ) * β + (q : ℤ) * d
            = (q : ℤ) * (W.R : ℤ) * (α + c) * (j' : ℤ)
              + (-((W.R : ℤ) * α * (j' : ℤ)) + (W.R : ℤ) * β + (q : ℤ) * e) * (q : ℤ)
          linear_combination (q : ℤ) * he
  | some j =>

    by_cases hpiv : (q : ℤ) ∣ (α + (j : ℤ) * ((W.R : ℤ) * c))
    ·
      obtain ⟨e, he⟩ := hpiv
      have hdetδ : Matrix.det
          !![-((W.R : ℤ) * β) - (W.R : ℤ) * d * (j : ℤ) + (q : ℤ) * e,
             W.a * β + W.a * d * (j : ℤ) - W.b * e;
             (q : ℤ) * (W.R : ℤ) * (c - d), -((W.R : ℤ) * W.b * c) + (q : ℤ) * W.a * d] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdet'
          + (-((W.R : ℤ) * β * c) - (W.R : ℤ) * c * d * (j : ℤ) + d * e * (q : ℤ)) * W.bezout
          + (-d) * he
      refine ⟨⟨_, hdetδ⟩, ?_, none, ?_⟩
      · rw [Gamma0_mem]; exact hmemM (c - d)
      · rw [traceRepMat_some, traceRepMat_none, hgmat]
        show _ = _ * W.mat
        rw [ALData.mat, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show 1 * α + (j : ℤ) * ((W.R : ℤ) * c)
            = (-((W.R : ℤ) * β) - (W.R : ℤ) * d * (j : ℤ) + (q : ℤ) * e) * ((q : ℤ) * W.a)
              + (W.a * β + W.a * d * (j : ℤ) - W.b * e) * ((q : ℤ) * (W.R : ℤ))
          linear_combination he + (-((q : ℤ) * e)) * W.bezout
        · show 1 * β + (j : ℤ) * d
            = (-((W.R : ℤ) * β) - (W.R : ℤ) * d * (j : ℤ) + (q : ℤ) * e) * W.b
              + (W.a * β + W.a * d * (j : ℤ) - W.b * e) * (q : ℤ)
          linear_combination (-(β + d * (j : ℤ))) * W.bezout
        · show 0 * α + (q : ℤ) * ((W.R : ℤ) * c)
            = (q : ℤ) * (W.R : ℤ) * (c - d) * ((q : ℤ) * W.a)
              + (-((W.R : ℤ) * W.b * c) + (q : ℤ) * W.a * d) * ((q : ℤ) * (W.R : ℤ))
          linear_combination (-((q : ℤ) * (W.R : ℤ) * c)) * W.bezout
        · show 0 * β + (q : ℤ) * d
            = (q : ℤ) * (W.R : ℤ) * (c - d) * W.b
              + (-((W.R : ℤ) * W.b * c) + (q : ℤ) * W.a * d) * (q : ℤ)
          linear_combination (-((q : ℤ) * d)) * W.bezout
    ·
      obtain ⟨j', hj'⟩ := exists_fin_dvd_sub_mul hq (β + (j : ℤ) * d) hpiv
      obtain ⟨e, he⟩ := hj'
      have hdetδ : Matrix.det
          !![α + (j : ℤ) * ((W.R : ℤ) * c), e;
             (q : ℤ) * (W.R : ℤ) * c, d - (W.R : ℤ) * c * (j' : ℤ)] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdet' + ((W.R : ℤ) * c) * he
      refine ⟨⟨_, hdetδ⟩, ?_, some j', ?_⟩
      · rw [Gamma0_mem]; exact hmemM c
      · rw [traceRepMat_some, traceRepMat_some, hgmat]
        rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show 1 * α + (j : ℤ) * ((W.R : ℤ) * c)
            = (α + (j : ℤ) * ((W.R : ℤ) * c)) * 1 + e * 0
          ring
        · show 1 * β + (j : ℤ) * d
            = (α + (j : ℤ) * ((W.R : ℤ) * c)) * (j' : ℤ) + e * (q : ℤ)
          linear_combination he
        · show 0 * α + (q : ℤ) * ((W.R : ℤ) * c)
            = (q : ℤ) * (W.R : ℤ) * c * 1 + (d - (W.R : ℤ) * c * (j' : ℤ)) * 0
          ring
        · show 0 * β + (q : ℤ) * d
            = (q : ℤ) * (W.R : ℤ) * c * (j' : ℤ) + (d - (W.R : ℤ) * c * (j' : ℤ)) * (q : ℤ)
          ring

end ModularCurve.ALData
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm"
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm"

namespace HeckeAnalytic

open ModularCurve

variable {M q : ℕ} (W : ALData M q)

def traceRepGL [NeZero M] [NeZero q] : Option (Fin q) → GL (Fin 2) ℝ
  | Option.none => alGL W
  | Option.some j => repGL q (Option.some j)

@[scoped simp] lemma traceRepGL_none [NeZero M] [NeZero q] : traceRepGL W none = alGL W := rfl

@[scoped simp] lemma traceRepGL_some [NeZero M] [NeZero q] (j : Fin q) :
    traceRepGL W (some j) = repGL q (some j) := rfl

lemma traceRepGL_coe [NeZero M] [NeZero q] (i : Option (Fin q)) :
    (traceRepGL W i : Matrix (Fin 2) (Fin 2) ℝ)
      = (W.traceRepMat i).map (algebraMap ℤ ℝ) := by
  cases i with
  | none => exact alGL_coe W
  | some j => exact repGL_coe q (some j)

def traceSlashSum (k : ℤ) [NeZero M] [NeZero q] (f : ℍ → ℂ) : ℍ → ℂ :=
  f + heckeUSlashSum k q (alSlash W k f)

lemma traceSlashSum_def (k : ℤ) [NeZero M] [NeZero q] (f : ℍ → ℂ) :
    traceSlashSum W k f = f + heckeUSlashSum k q (alSlash W k f) := rfl

lemma traceSlashSum_add (k : ℤ) [NeZero M] [NeZero q] (f g : ℍ → ℂ) :
    traceSlashSum W k (f + g) = traceSlashSum W k f + traceSlashSum W k g := by
  simp only [traceSlashSum, HeckeAnalytic.alSlash_add, heckeUSlashSum_add]
  abel

lemma traceSlashSum_smul (k : ℤ) [NeZero M] [NeZero q] (c : ℂ) (f : ℍ → ℂ) :
    traceSlashSum W k (c • f) = c • traceSlashSum W k f := by
  simp only [traceSlashSum, HeckeAnalytic.alSlash_smul, heckeUSlashSum_smul, smul_add]

lemma traceSlashSum_eq_sum_traceRepGL [NeZero M] [NeZero q] {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      f ∣[(2 : ℤ)] γ = f) :
    traceSlashSum W 2 f
      = ∑ i : Option (Fin q), (alSlash W 2 f) ∣[(2 : ℤ)] traceRepGL W i := by
  rw [Fintype.sum_option]
  show traceSlashSum W 2 f
    = (alSlash W 2 f) ∣[(2 : ℤ)] alGL W + ∑ j : Fin q, (alSlash W 2 f) ∣[(2 : ℤ)] repGL q (some j)
  rw [traceSlashSum_def]
  congr 1
  exact (alSlash_alSlash_two W hf).symm

private lemma mapGL_coe_eq' (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

private lemma map_int_mul_eq' (A P : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * P).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

private lemma traceRepGL_cocycle_of_int [NeZero M] [NeZero q] {g δ : SL(2, ℤ)}
    {i i' : Option (Fin q)}
    (hint : W.traceRepMat i * (g : Matrix (Fin 2) (Fin 2) ℤ)
      = (δ : Matrix (Fin 2) (Fin 2) ℤ) * W.traceRepMat i') :
    traceRepGL W i * Matrix.SpecialLinearGroup.mapGL ℝ g
      = Matrix.SpecialLinearGroup.mapGL ℝ δ * traceRepGL W i' := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (traceRepGL W i : Matrix (Fin 2) (Fin 2) ℝ) *
      ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
    = ((Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
      (traceRepGL W i' : Matrix (Fin 2) (Fin 2) ℝ)
  rw [traceRepGL_coe, traceRepGL_coe, mapGL_coe_eq', mapGL_coe_eq', ← map_int_mul_eq',
    ← map_int_mul_eq', hint]

theorem traceSlashSum_slash [NeZero M] [NeZero q] (hq : q.Prime) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      f ∣[(2 : ℤ)] γ = f)
    {γ : GL (Fin 2) ℝ}
    (hγ : γ ∈ ((Gamma0 W.R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    (traceSlashSum W 2 f) ∣[(2 : ℤ)] γ = traceSlashSum W 2 f := by

  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ

  choose δ hδ m hm using W.exists_traceRep_cocycle hq hg

  have hinj : Function.Injective m := by
    intro i₁ i₂ him
    have h₁ := hm i₁
    have h₂ := hm i₂
    rw [him] at h₁
    have hg_inv : (g : Matrix (Fin 2) (Fin 2) ℤ) * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hδ₂ : (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        ((δ i₂ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hcomb : W.traceRepMat i₁ =
        ((δ i₁ * (δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * W.traceRepMat i₂ := by
      have step : W.traceRepMat i₁ * (g : Matrix (Fin 2) (Fin 2) ℤ) =
          (((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
            (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
            (W.traceRepMat i₂ * (g : Matrix (Fin 2) (Fin 2) ℤ)) := by
        calc W.traceRepMat i₁ * (g : Matrix (Fin 2) (Fin 2) ℤ)
            = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * W.traceRepMat (m i₂) := h₁
          _ = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                ((((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                  (((δ i₂ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                    W.traceRepMat (m i₂))) := by
              rw [← mul_assoc (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), hδ₂, one_mul]
          _ = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                ((((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                  (W.traceRepMat i₂ * (g : Matrix (Fin 2) (Fin 2) ℤ))) := by rw [h₂]
          _ = (((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
                (W.traceRepMat i₂ * (g : Matrix (Fin 2) (Fin 2) ℤ)) := by
              simp only [mul_assoc]
      have := congrArg (· * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) step
      simp only [mul_assoc, hg_inv, mul_one] at this
      rw [this, Matrix.SpecialLinearGroup.coe_mul, mul_assoc]
    exact W.traceRepMat_unique hq.one_lt hcomb
  have hbij : Function.Bijective m := Finite.injective_iff_bijective.mp hinj

  have hmGL : ∀ i, traceRepGL W i * Matrix.SpecialLinearGroup.mapGL ℝ g =
      Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * traceRepGL W (m i) :=
    fun i => traceRepGL_cocycle_of_int W (hm i)

  rw [traceSlashSum_eq_sum_traceRepGL W hf]
  calc (∑ i : Option (Fin q), (alSlash W 2 f) ∣[(2 : ℤ)] traceRepGL W i)
        ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ g)
      = ∑ i : Option (Fin q), ((alSlash W 2 f) ∣[(2 : ℤ)] traceRepGL W i)
          ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ g) := by
        rw [SlashAction.sum_slash]
    _ = ∑ i : Option (Fin q), (alSlash W 2 f)
          ∣[(2 : ℤ)] (traceRepGL W i * Matrix.SpecialLinearGroup.mapGL ℝ g) := by
        simp_rw [SlashAction.slash_mul]
    _ = ∑ i : Option (Fin q), (alSlash W 2 f)
          ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * traceRepGL W (m i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hmGL i]
    _ = ∑ i : Option (Fin q), ((alSlash W 2 f)
          ∣[(2 : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ (δ i)) ∣[(2 : ℤ)] traceRepGL W (m i) := by
        simp_rw [SlashAction.slash_mul]
    _ = ∑ i : Option (Fin q), (alSlash W 2 f) ∣[(2 : ℤ)] traceRepGL W (m i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [alSlash_slash W hf (Subgroup.mem_map.mpr ⟨δ i, hδ i, rfl⟩)]
    _ = ∑ i : Option (Fin q), (alSlash W 2 f) ∣[(2 : ℤ)] traceRepGL W i :=
        hbij.sum_comp fun i => (alSlash W 2 f) ∣[(2 : ℤ)] traceRepGL W i

lemma slash_alGL_inv_two [NeZero M] {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      f ∣[(2 : ℤ)] γ = f) :
    f ∣[(2 : ℤ)] (alGL W)⁻¹ = alSlash W 2 f := by
  conv_lhs => rw [← alSlash_alSlash_two W hf]
  show ((alSlash W 2 f) ∣[(2 : ℤ)] alGL W) ∣[(2 : ℤ)] (alGL W)⁻¹ = alSlash W 2 f
  rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

theorem slash_eq_traceTerm_of_classified [NeZero M] [NeZero q] {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      f ∣[(2 : ℤ)] γ = f)
    {g δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 M) {i : Option (Fin q)}
    (hint : W.mat * (g : Matrix (Fin 2) (Fin 2) ℤ)
      = (δ : Matrix (Fin 2) (Fin 2) ℤ) * W.traceRepMat i) :
    f ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ g)
      = (alSlash W 2 f) ∣[(2 : ℤ)] traceRepGL W i := by

  have hGL : alGL W * Matrix.SpecialLinearGroup.mapGL ℝ g
      = Matrix.SpecialLinearGroup.mapGL ℝ δ * traceRepGL W i :=
    traceRepGL_cocycle_of_int W (i := none) hint
  have hsolve : Matrix.SpecialLinearGroup.mapGL ℝ g
      = (alGL W)⁻¹ * (Matrix.SpecialLinearGroup.mapGL ℝ δ * traceRepGL W i) := by
    rw [← hGL, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hsolve, SlashAction.slash_mul, slash_alGL_inv_two W hf, SlashAction.slash_mul,
    alSlash_slash W hf (Subgroup.mem_map.mpr ⟨δ, hδ, rfl⟩)]

theorem traceSlashSum_eq_sum_repr [NeZero M] [NeZero q] {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      f ∣[(2 : ℤ)] γ = f)
    {ρ : Option (Fin q) → SL(2, ℤ)} {δ : Option (Fin q) → SL(2, ℤ)}
    (hδ : ∀ i, δ i ∈ Gamma0 M)
    (hclass : ∀ i, W.mat * (ρ i : Matrix (Fin 2) (Fin 2) ℤ)
      = (δ i : Matrix (Fin 2) (Fin 2) ℤ) * W.traceRepMat i) :
    traceSlashSum W 2 f
      = ∑ i : Option (Fin q), f ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (ρ i)) := by
  rw [traceSlashSum_eq_sum_traceRepGL W hf]
  exact (Finset.sum_congr rfl fun i _ =>
    slash_eq_traceTerm_of_classified W hf (hδ i) (hclass i)).symm

theorem traceSlashSum_alSlash (k : ℤ) [NeZero M] [NeZero q] {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) :
    traceSlashSum W k (alSlash W k f)
      = alSlash W k f + ((q : ℂ) ^ (k - 2)) • heckeUSlashSum k q f := by
  rw [traceSlashSum_def, alSlash_alSlash W k hf, heckeUSlashSum_smul]

theorem traceSlashSum_alSlash_two [NeZero M] [NeZero q] {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      f ∣[(2 : ℤ)] γ = f) :
    traceSlashSum W 2 (alSlash W 2 f) = alSlash W 2 f + heckeUSlashSum 2 q f := by
  rw [traceSlashSum_alSlash W 2 hf]
  norm_num

open OnePoint

lemma traceSlashSum_mdiff (k : ℤ) [NeZero M] [NeZero q] {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (traceSlashSum W k f) :=
  hf.add (heckeUSlashSum_mdiff (alSlash_mdiff W hf))

lemma isCusp_gamma0_iff (N N' : ℕ) [NeZero N] [NeZero N'] {c : OnePoint ℝ} :
    IsCusp c ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
      ↔ IsCusp c ((Gamma0 N' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Iff.trans (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _)
    (Iff.symm (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _))

lemma traceSlashSum_isZeroAt (k : ℤ) [NeZero M] [NeZero q] {f : ℍ → ℂ}
    (hf : ∀ c' : OnePoint ℝ,
      IsCusp c' ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) →
      IsZeroAt c' f k)
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 W.R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsZeroAt c (traceSlashSum W k f) k := by
  haveI : NeZero W.R := ⟨W.R_pos.ne'⟩
  have hcM : IsCusp c ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    (isCusp_gamma0_iff W.R M).mp hc
  exact (hf c hcM).add
    (heckeUSlashSum_isZeroAt (N := M) (fun _ hc' => alSlash_isZeroAt W hf hc') hcM)

end HeckeAnalytic
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm"

namespace CuspForm

open HeckeAnalytic ModularCurve CongruenceSubgroup OnePoint

variable {M q : ℕ} [NeZero M]

def traceMap (W : ALData M q) (hq : q.Prime) (f : CuspForm (Gamma0 M) 2) :
    CuspForm (Gamma0 W.R) 2 :=
  haveI : NeZero q := ⟨hq.ne_zero⟩
  { toFun := traceSlashSum W 2 f
    slash_action_eq' := fun _ hγ => traceSlashSum_slash W hq f.slash_action_eq' hγ
    holo' := traceSlashSum_mdiff W 2 f.holo'
    zero_at_cusps' := fun hc =>
      traceSlashSum_isZeroAt W 2 (fun _ hc' => f.zero_at_cusps' hc') hc }

lemma traceMap_coe (W : ALData M q) (hq : q.Prime) (f : CuspForm (Gamma0 M) 2) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ⇑(traceMap W hq f) = traceSlashSum W 2 ⇑f := rfl

lemma traceMap_add (W : ALData M q) (hq : q.Prime) (f g : CuspForm (Gamma0 M) 2) :
    traceMap W hq (f + g) = traceMap W hq f + traceMap W hq g := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  ext τ
  show traceSlashSum W 2 (⇑f + ⇑g) τ = (traceSlashSum W 2 ⇑f + traceSlashSum W 2 ⇑g) τ
  rw [traceSlashSum_add]

lemma traceMap_smul (W : ALData M q) (hq : q.Prime) (c : ℂ) (f : CuspForm (Gamma0 M) 2) :
    traceMap W hq (c • f) = c • traceMap W hq f := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  ext τ
  show traceSlashSum W 2 (c • ⇑f) τ = (c • traceSlashSum W 2 ⇑f) τ
  rw [traceSlashSum_smul]

def traceMapHom (W : ALData M q) (hq : q.Prime) :
    CuspForm (Gamma0 M) 2 →ₗ[ℂ] CuspForm (Gamma0 W.R) 2 where
  toFun := traceMap W hq
  map_add' := traceMap_add W hq
  map_smul' := traceMap_smul W hq

@[scoped simp] lemma traceMapHom_apply (W : ALData M q) (hq : q.Prime) (f : CuspForm (Gamma0 M) 2) :
    traceMapHom W hq f = traceMap W hq f := rfl

theorem traceMap_atkinLehner (W : ALData M q) (hq : q.Prime) (f : CuspForm (Gamma0 M) 2) :
    ⇑(traceMap W hq (atkinLehner W f))
      = ⇑(atkinLehner W f) + ⇑(heckeU q hq ⟨W.R, W.hM⟩ f) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  show traceSlashSum W 2 (alSlash W 2 ⇑f) = alSlash W 2 ⇑f + heckeUSlashSum 2 q ⇑f
  exact traceSlashSum_alSlash_two W f.slash_action_eq'

end CuspForm
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm"

end
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm"

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped MatrixGroups ModularForm

noncomputable section

namespace HeckeAnalytic

open ModularCurve

private lemma exists_fin_dvd_sub {ℓ : ℕ} (hℓ : ℓ.Prime) (p t : ℤ) (hp : ¬ (ℓ : ℤ) ∣ p) :
    ∃ j' : Fin ℓ, (ℓ : ℤ) ∣ t - p * (j' : ℤ) := by
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hℓpos : (0 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ.pos
  have hcop : IsCoprime (ℓ : ℤ) p :=
    (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ)).mpr hp
  obtain ⟨u, v, huv⟩ := hcop
  have hmod := Int.emod_add_mul_ediv (v * t) (ℓ : ℤ)
  have hnonneg : 0 ≤ (v * t) % (ℓ : ℤ) := Int.emod_nonneg _ hℓ0
  have hlt : (v * t) % (ℓ : ℤ) < (ℓ : ℤ) := Int.emod_lt_of_pos _ hℓpos
  have hcoe : ((((v * t) % (ℓ : ℤ)).toNat : ℕ) : ℤ) = (v * t) % (ℓ : ℤ) :=
    Int.toNat_of_nonneg hnonneg
  refine ⟨⟨((v * t) % (ℓ : ℤ)).toNat, by omega⟩,
    ⟨t * u + p * ((v * t) / (ℓ : ℤ)), ?_⟩⟩
  show t - p * ((((v * t) % (ℓ : ℤ)).toNat : ℕ) : ℤ) = (ℓ : ℤ) * (t * u + p * ((v * t) / (ℓ : ℤ)))
  rw [hcoe]
  linear_combination (-t) * huv + (-p) * hmod

lemma map_int_mul' (A P : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * P).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

variable {M q : ℕ}

lemma exists_cocycle_hecke_al {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (W : ALData M q)
    (i : Option (Fin ℓ)) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 M ∧ ∃ m : Option (Fin ℓ),
      repMat ℓ i * W.mat = (δ : Matrix (Fin 2) (Fin 2) ℤ) * (W.mat * repMat ℓ m) := by

  have hℓq : ¬ ℓ ∣ q := fun h => hℓM (W.hM ▸ h.mul_right W.R)
  have hℓR : ¬ ℓ ∣ W.R := fun h => hℓM (W.hM ▸ h.mul_left q)
  have hℓqZ : ¬ (ℓ : ℤ) ∣ (q : ℤ) := fun h => hℓq (Int.natCast_dvd_natCast.mp h)
  have hℓRZ : ¬ (ℓ : ℤ) ∣ (W.R : ℤ) := fun h => hℓR (Int.natCast_dvd_natCast.mp h)
  cases i with
  | none =>

    obtain ⟨j', e, he⟩ := exists_fin_dvd_sub hℓ (W.R : ℤ) 1 hℓRZ

    have hdetδ : Matrix.det
        !![W.a * ((q : ℤ) * (W.R : ℤ)) * (j' : ℤ) + (q : ℤ) * W.a * ((ℓ : ℤ) - 1) + 1,
             -((q : ℤ) * W.a ^ 2 * (j' : ℤ)) + W.a * W.b * (1 - (ℓ : ℤ));
           (q : ℤ) * (W.R : ℤ) * (1 - e),
             W.a * (q : ℤ) * e - (W.R : ℤ) * W.b] = 1 := by
      rw [Matrix.det_fin_two_of]
      linear_combination
        ((W.R : ℤ) * W.a * (j' : ℤ) * (q : ℤ) + (W.R : ℤ) * (j' : ℤ)
            + W.a * e * (ℓ : ℤ) * (q : ℤ) - W.a * e * (q : ℤ) + e * (ℓ : ℤ)) * W.bezout
          + (-(W.R : ℤ) * W.b - 1) * he
    refine ⟨⟨_, hdetδ⟩, ?_, some j', ?_⟩
    · rw [Gamma0_mem]
      show ((((q : ℤ) * (W.R : ℤ) * (1 - e) : ℤ)) : ZMod M) = 0
      rw [← W.hM_int]
      push_cast
      simp
    · show repMat ℓ none * W.mat
        = !![W.a * ((q : ℤ) * (W.R : ℤ)) * (j' : ℤ) + (q : ℤ) * W.a * ((ℓ : ℤ) - 1) + 1,
               -((q : ℤ) * W.a ^ 2 * (j' : ℤ)) + W.a * W.b * (1 - (ℓ : ℤ));
             (q : ℤ) * (W.R : ℤ) * (1 - e),
               W.a * (q : ℤ) * e - (W.R : ℤ) * W.b] * (W.mat * repMat ℓ (some j'))
      rw [repMat_none, repMat_some, ALData.mat, Matrix.mul_fin_two, Matrix.mul_fin_two,
        Matrix.mul_fin_two]
      refine Matrix.ext fun x y => ?_
      fin_cases x <;> fin_cases y
      · show ((ℓ : ℤ) * ((q : ℤ) * W.a) + 0 * ((q : ℤ) * (W.R : ℤ)) : ℤ)
          = (W.a * ((q : ℤ) * (W.R : ℤ)) * (j' : ℤ) + (q : ℤ) * W.a * ((ℓ : ℤ) - 1) + 1)
                * ((q : ℤ) * W.a * 1 + W.b * 0)
            + (-((q : ℤ) * W.a ^ 2 * (j' : ℤ)) + W.a * W.b * (1 - (ℓ : ℤ)))
                * ((q : ℤ) * (W.R : ℤ) * 1 + (q : ℤ) * 0)
        linear_combination (-(W.a * (q : ℤ) * ((ℓ : ℤ) - 1))) * W.bezout
      · show ((ℓ : ℤ) * W.b + 0 * (q : ℤ) : ℤ)
          = (W.a * ((q : ℤ) * (W.R : ℤ)) * (j' : ℤ) + (q : ℤ) * W.a * ((ℓ : ℤ) - 1) + 1)
                * ((q : ℤ) * W.a * (j' : ℤ) + W.b * (ℓ : ℤ))
            + (-((q : ℤ) * W.a ^ 2 * (j' : ℤ)) + W.a * W.b * (1 - (ℓ : ℤ)))
                * ((q : ℤ) * (W.R : ℤ) * (j' : ℤ) + (q : ℤ) * (ℓ : ℤ))
        linear_combination (W.a * (j' : ℤ) * (q : ℤ)) * W.bezout
      · show (0 * ((q : ℤ) * W.a) + 1 * ((q : ℤ) * (W.R : ℤ)) : ℤ)
          = (q : ℤ) * (W.R : ℤ) * (1 - e) * ((q : ℤ) * W.a * 1 + W.b * 0)
            + (W.a * (q : ℤ) * e - (W.R : ℤ) * W.b)
                * ((q : ℤ) * (W.R : ℤ) * 1 + (q : ℤ) * 0)
        linear_combination (-(W.R : ℤ) * (q : ℤ)) * W.bezout
      · show (0 * W.b + 1 * (q : ℤ) : ℤ)
          = (q : ℤ) * (W.R : ℤ) * (1 - e) * ((q : ℤ) * W.a * (j' : ℤ) + W.b * (ℓ : ℤ))
            + (W.a * (q : ℤ) * e - (W.R : ℤ) * W.b)
                * ((q : ℤ) * (W.R : ℤ) * (j' : ℤ) + (q : ℤ) * (ℓ : ℤ))
        linear_combination (-(q : ℤ) * ((W.R : ℤ) * (j' : ℤ) + e * (ℓ : ℤ))) * W.bezout
          + (q : ℤ) * he
  | some j =>
    by_cases hdvd : (ℓ : ℤ) ∣ (W.a + (j : ℤ) * (W.R : ℤ))
    ·
      obtain ⟨e, he⟩ := hdvd

      have hdetδ : Matrix.det
          !![(q : ℤ) * e - (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) - W.b * (W.R : ℤ),
               W.a * W.b + (j : ℤ) * (q : ℤ) * W.a - W.b * e;
             (q : ℤ) * (W.R : ℤ) * (1 - (ℓ : ℤ)),
               (ℓ : ℤ) * (q : ℤ) * W.a - (W.R : ℤ) * W.b] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination
          (-(W.R : ℤ) * W.b - (W.R : ℤ) * (j : ℤ) * (q : ℤ) + e * (ℓ : ℤ) * (q : ℤ) + 1)
              * W.bezout
            + (-(q : ℤ)) * he
      refine ⟨⟨_, hdetδ⟩, ?_, none, ?_⟩
      · rw [Gamma0_mem]
        show ((((q : ℤ) * (W.R : ℤ) * (1 - (ℓ : ℤ)) : ℤ)) : ZMod M) = 0
        rw [← W.hM_int]
        push_cast
        simp
      · show repMat ℓ (some j) * W.mat
          = !![(q : ℤ) * e - (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) - W.b * (W.R : ℤ),
                 W.a * W.b + (j : ℤ) * (q : ℤ) * W.a - W.b * e;
               (q : ℤ) * (W.R : ℤ) * (1 - (ℓ : ℤ)),
                 (ℓ : ℤ) * (q : ℤ) * W.a - (W.R : ℤ) * W.b] * (W.mat * repMat ℓ none)
        rw [repMat_some, repMat_none, ALData.mat, Matrix.mul_fin_two, Matrix.mul_fin_two,
          Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show (1 * ((q : ℤ) * W.a) + (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) : ℤ)
            = ((q : ℤ) * e - (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) - W.b * (W.R : ℤ))
                  * ((q : ℤ) * W.a * (ℓ : ℤ) + W.b * 0)
              + (W.a * W.b + (j : ℤ) * (q : ℤ) * W.a - W.b * e)
                  * ((q : ℤ) * (W.R : ℤ) * (ℓ : ℤ) + (q : ℤ) * 0)
          linear_combination (-e * (ℓ : ℤ) * (q : ℤ)) * W.bezout + (q : ℤ) * he
        · show (1 * W.b + (j : ℤ) * (q : ℤ) : ℤ)
            = ((q : ℤ) * e - (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) - W.b * (W.R : ℤ))
                  * ((q : ℤ) * W.a * 0 + W.b * 1)
              + (W.a * W.b + (j : ℤ) * (q : ℤ) * W.a - W.b * e)
                  * ((q : ℤ) * (W.R : ℤ) * 0 + (q : ℤ) * 1)
          linear_combination (-W.b - (j : ℤ) * (q : ℤ)) * W.bezout
        · show (0 * ((q : ℤ) * W.a) + (ℓ : ℤ) * ((q : ℤ) * (W.R : ℤ)) : ℤ)
            = (q : ℤ) * (W.R : ℤ) * (1 - (ℓ : ℤ)) * ((q : ℤ) * W.a * (ℓ : ℤ) + W.b * 0)
              + ((ℓ : ℤ) * (q : ℤ) * W.a - (W.R : ℤ) * W.b)
                  * ((q : ℤ) * (W.R : ℤ) * (ℓ : ℤ) + (q : ℤ) * 0)
          linear_combination (-(W.R : ℤ) * (ℓ : ℤ) * (q : ℤ)) * W.bezout
        · show (0 * W.b + (ℓ : ℤ) * (q : ℤ) : ℤ)
            = (q : ℤ) * (W.R : ℤ) * (1 - (ℓ : ℤ)) * ((q : ℤ) * W.a * 0 + W.b * 1)
              + ((ℓ : ℤ) * (q : ℤ) * W.a - (W.R : ℤ) * W.b)
                  * ((q : ℤ) * (W.R : ℤ) * 0 + (q : ℤ) * 1)
          linear_combination (-(ℓ : ℤ) * (q : ℤ)) * W.bezout
    ·

      have hpu : ¬ (ℓ : ℤ) ∣ (q : ℤ) * (W.a + (j : ℤ) * (W.R : ℤ)) := by
        intro h
        rcases (Nat.prime_iff_prime_int.mp hℓ).dvd_mul.mp h with h' | h'
        · exact hℓqZ h'
        · exact hdvd h'
      obtain ⟨j', e, he⟩ := exists_fin_dvd_sub hℓ ((q : ℤ) * (W.a + (j : ℤ) * (W.R : ℤ)))
        (W.b + (j : ℤ) * (q : ℤ)) hpu

      have hdetδ : Matrix.det
          !![(q : ℤ) * W.a + (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) - (W.R : ℤ) * e,
               W.a * e - W.a * W.b - (j : ℤ) * (W.R : ℤ) * W.b;
             (q : ℤ) * (W.R : ℤ) * ((W.R : ℤ) * (j' : ℤ) + (ℓ : ℤ) - 1),
               (q : ℤ) * W.a - ((q : ℤ) * (W.R : ℤ)) * W.a * (j' : ℤ)
                 - (ℓ : ℤ) * (W.R : ℤ) * W.b] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination
          (-(W.R : ℤ) * e * (ℓ : ℤ) + (W.R : ℤ) * (j : ℤ) * (q : ℤ)
              - (W.R : ℤ) * (j' : ℤ) * (q : ℤ) * ((W.R : ℤ) * (j : ℤ) + W.a)
              + W.a * (q : ℤ) + 1) * W.bezout
            + (W.R : ℤ) * he
      refine ⟨⟨_, hdetδ⟩, ?_, some j', ?_⟩
      · rw [Gamma0_mem]
        show ((((q : ℤ) * (W.R : ℤ) * ((W.R : ℤ) * (j' : ℤ) + (ℓ : ℤ) - 1) : ℤ)) : ZMod M) = 0
        rw [← W.hM_int]
        push_cast
        simp
      · show repMat ℓ (some j) * W.mat
          = !![(q : ℤ) * W.a + (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) - (W.R : ℤ) * e,
                 W.a * e - W.a * W.b - (j : ℤ) * (W.R : ℤ) * W.b;
               (q : ℤ) * (W.R : ℤ) * ((W.R : ℤ) * (j' : ℤ) + (ℓ : ℤ) - 1),
                 (q : ℤ) * W.a - ((q : ℤ) * (W.R : ℤ)) * W.a * (j' : ℤ)
                   - (ℓ : ℤ) * (W.R : ℤ) * W.b] * (W.mat * repMat ℓ (some j'))
        rw [repMat_some, repMat_some, ALData.mat, Matrix.mul_fin_two, Matrix.mul_fin_two,
          Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show (1 * ((q : ℤ) * W.a) + (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) : ℤ)
            = ((q : ℤ) * W.a + (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) - (W.R : ℤ) * e)
                  * ((q : ℤ) * W.a * 1 + W.b * 0)
              + (W.a * e - W.a * W.b - (j : ℤ) * (W.R : ℤ) * W.b)
                  * ((q : ℤ) * (W.R : ℤ) * 1 + (q : ℤ) * 0)
          linear_combination (-(q : ℤ) * ((W.R : ℤ) * (j : ℤ) + W.a)) * W.bezout
        · show (1 * W.b + (j : ℤ) * (q : ℤ) : ℤ)
            = ((q : ℤ) * W.a + (j : ℤ) * ((q : ℤ) * (W.R : ℤ)) - (W.R : ℤ) * e)
                  * ((q : ℤ) * W.a * (j' : ℤ) + W.b * (ℓ : ℤ))
              + (W.a * e - W.a * W.b - (j : ℤ) * (W.R : ℤ) * W.b)
                  * ((q : ℤ) * (W.R : ℤ) * (j' : ℤ) + (q : ℤ) * (ℓ : ℤ))
          linear_combination
            (-e * (ℓ : ℤ) - (j' : ℤ) * (q : ℤ) * ((W.R : ℤ) * (j : ℤ) + W.a)) * W.bezout + he
        · show (0 * ((q : ℤ) * W.a) + (ℓ : ℤ) * ((q : ℤ) * (W.R : ℤ)) : ℤ)
            = (q : ℤ) * (W.R : ℤ) * ((W.R : ℤ) * (j' : ℤ) + (ℓ : ℤ) - 1)
                  * ((q : ℤ) * W.a * 1 + W.b * 0)
              + ((q : ℤ) * W.a - ((q : ℤ) * (W.R : ℤ)) * W.a * (j' : ℤ)
                  - (ℓ : ℤ) * (W.R : ℤ) * W.b)
                  * ((q : ℤ) * (W.R : ℤ) * 1 + (q : ℤ) * 0)
          linear_combination (-(W.R : ℤ) * (ℓ : ℤ) * (q : ℤ)) * W.bezout
        · show (0 * W.b + (ℓ : ℤ) * (q : ℤ) : ℤ)
            = (q : ℤ) * (W.R : ℤ) * ((W.R : ℤ) * (j' : ℤ) + (ℓ : ℤ) - 1)
                  * ((q : ℤ) * W.a * (j' : ℤ) + W.b * (ℓ : ℤ))
              + ((q : ℤ) * W.a - ((q : ℤ) * (W.R : ℤ)) * W.a * (j' : ℤ)
                  - (ℓ : ℤ) * (W.R : ℤ) * W.b)
                  * ((q : ℤ) * (W.R : ℤ) * (j' : ℤ) + (q : ℤ) * (ℓ : ℤ))
          linear_combination (-(ℓ : ℤ) * (q : ℤ)) * W.bezout

theorem alSlash_heckeSlashSum {k : ℤ} {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    [NeZero M] (W : ALData M q) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) :
    alSlash W k (heckeSlashSum k ℓ f) = heckeSlashSum k ℓ (alSlash W k f) := by

  choose δ hδ m hm using exists_cocycle_hecke_al hℓ hℓM W

  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast W.q_pos.ne'
  have hinj : Function.Injective m := by
    intro i₁ i₂ him

    have hδ₁ : (((δ i₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h₁ := hm i₁
    have h₂ := hm i₂
    rw [him] at h₁

    have hWm : W.mat * repMat ℓ (m i₂)
        = (((δ i₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (repMat ℓ i₁ * W.mat) := by
      rw [h₁, ← mul_assoc, hδ₁, one_mul]

    have hcomb : repMat ℓ i₂ * W.mat
        = ((δ i₂ * (δ i₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ i₁ * W.mat := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      calc repMat ℓ i₂ * W.mat
          = (δ i₂ : Matrix (Fin 2) (Fin 2) ℤ) * (W.mat * repMat ℓ (m i₂)) := h₂
        _ = (δ i₂ : Matrix (Fin 2) (Fin 2) ℤ)
              * ((((δ i₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
                  * (repMat ℓ i₁ * W.mat)) := by rw [hWm]
        _ = (δ i₂ : Matrix (Fin 2) (Fin 2) ℤ)
              * (((δ i₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ i₁ * W.mat := by
            simp only [mul_assoc]

    have hadj := congrArg (· * W.mat.adjugate) hcomb
    simp only [mul_assoc, Matrix.mul_adjugate, ALData.det_mat, Matrix.mul_smul, mul_one] at hadj
    have hXY : repMat ℓ i₂
        = ((δ i₂ * (δ i₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ i₁ := by
      refine Matrix.ext fun x y => mul_left_cancel₀ hq0 ?_
      have hxy := congrFun (congrFun hadj x) y
      simpa [Matrix.smul_apply, smul_eq_mul, mul_assoc] using hxy
    exact (repMat_unique hℓ.one_lt hXY).symm
  have hbij : Function.Bijective m := Finite.injective_iff_bijective.mp hinj

  have hmGL : ∀ i, repGL ℓ i * alGL W
      = Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * (alGL W * repGL ℓ (m i)) := by
    intro i
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul]
    show (repGL ℓ i : Matrix (Fin 2) (Fin 2) ℝ) * (alGL W : Matrix (Fin 2) (Fin 2) ℝ)
      = ((δ i : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ)
          * ((alGL W : Matrix (Fin 2) (Fin 2) ℝ) * (repGL ℓ (m i) : Matrix (Fin 2) (Fin 2) ℝ))
    rw [repGL_coe, repGL_coe, alGL_coe, ← map_int_mul' (repMat ℓ i) W.mat,
      ← map_int_mul' W.mat (repMat ℓ (m i)), ← map_int_mul', hm i]

  calc alSlash W k (heckeSlashSum k ℓ f)
      = ∑ i : Option (Fin ℓ), (f ∣[k] repGL ℓ i) ∣[k] alGL W := by
        rw [alSlash, heckeSlashSum, SlashAction.sum_slash]
    _ = ∑ i : Option (Fin ℓ), f ∣[k] (repGL ℓ i * alGL W) := by
        simp_rw [SlashAction.slash_mul]
    _ = ∑ i : Option (Fin ℓ),
          f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * (alGL W * repGL ℓ (m i))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hmGL i]
    _ = ∑ i : Option (Fin ℓ),
          ((f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ (δ i)) ∣[k] alGL W) ∣[k] repGL ℓ (m i) := by
        simp_rw [SlashAction.slash_mul]
    _ = ∑ i : Option (Fin ℓ), (f ∣[k] alGL W) ∣[k] repGL ℓ (m i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hf (Matrix.SpecialLinearGroup.mapGL ℝ (δ i)) (Subgroup.mem_map.mpr ⟨δ i, hδ i, rfl⟩)]
    _ = ∑ i : Option (Fin ℓ), (f ∣[k] alGL W) ∣[k] repGL ℓ i :=
        hbij.sum_comp fun i => (f ∣[k] alGL W) ∣[k] repGL ℓ i
    _ = heckeSlashSum k ℓ (alSlash W k f) := rfl

end HeckeAnalytic
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm"

namespace ModularCurve
namespace ALData

variable {M q : ℕ}

theorem exists_gamma_mat_eq_mul [NeZero M] (W₁ W₂ : ALData M q) :
    ∃ u : SL(2, ℤ), u ∈ Gamma0 M ∧
      W₁.mat = (u : Matrix (Fin 2) (Fin 2) ℤ) * W₂.mat := by

  have hR : (W₁.R : ℤ) = (W₂.R : ℤ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℤ))
      (Nat.eq_of_mul_eq_mul_left W₁.q_pos (W₁.hM.symm.trans W₂.hM))
  set t : ℤ := W₂.a * W₁.b - W₁.a * W₂.b with ht
  have hdetu : Matrix.det !![(1 : ℤ), t; 0, 1] = 1 := by
    rw [Matrix.det_fin_two_of]; ring
  refine ⟨⟨_, hdetu⟩, ?_, ?_⟩
  · rw [Gamma0_mem]
    show (((0 : ℤ)) : ZMod M) = 0
    simp
  · show W₁.mat = !![(1 : ℤ), t; 0, 1] * W₂.mat
    rw [ALData.mat, ALData.mat, Matrix.mul_fin_two]
    refine Matrix.ext fun x y => ?_
    fin_cases x <;> fin_cases y
    · show ((q : ℤ) * W₁.a : ℤ) = 1 * ((q : ℤ) * W₂.a) + t * ((q : ℤ) * (W₂.R : ℤ))
      rw [ht]
      linear_combination ((W₂.R : ℤ) * W₂.b + 1) * W₁.bezout
        + (-(W₂.R : ℤ) * W₁.b - 1) * W₂.bezout + (W₁.b * ((W₂.R : ℤ) * W₂.b + 1)) * hR
    · show (W₁.b : ℤ) = 1 * W₂.b + t * (q : ℤ)
      rw [ht]
      linear_combination W₂.b * W₁.bezout + (-W₁.b) * W₂.bezout + (W₁.b * W₂.b) * hR
    · show ((q : ℤ) * (W₁.R : ℤ) : ℤ) = 0 * ((q : ℤ) * W₂.a) + 1 * ((q : ℤ) * (W₂.R : ℤ))
      linear_combination (q : ℤ) * hR
    · show ((q : ℤ) : ℤ) = 0 * W₂.b + 1 * (q : ℤ)
      ring

end ModularCurve.ALData
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm"
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm"

end
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm"

end WcPort
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort"

namespace WcPort
namespace HeckeAnalytic

open UpperHalfPlane
open scoped ModularForm MatrixGroups

open _root_.ModularForm in
theorem repGL_some_eq_heckeMatrix (ℓ : ℕ) [NeZero ℓ] (j : Fin ℓ) :
    repGL ℓ (some j) = heckeMatrix ℓ (j : ℕ) := by
  apply Units.ext
  rw [repGL_coe, val_heckeMatrix (NeZero.ne ℓ)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [repMat]

open _root_.ModularForm in
theorem repGL_none_eq_heckeDiagMatrix (ℓ : ℕ) [NeZero ℓ] :
    repGL ℓ none = heckeDiagMatrix ℓ := by
  apply Units.ext
  rw [repGL_coe, val_heckeDiagMatrix (NeZero.ne ℓ)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [repMat]

open _root_.ModularForm in
theorem heckeUSlashSum_eq_heckeU (k : ℤ) (ℓ : ℕ) [NeZero ℓ] (f : ℍ → ℂ) :
    heckeUSlashSum k ℓ f = heckeU k ℓ f := by
  rw [heckeUSlashSum, heckeU_def]
  rw [← Fin.sum_univ_eq_sum_range (fun j => f ∣[k] heckeMatrix ℓ j) ℓ]
  exact Finset.sum_congr rfl fun j _ => by rw [repGL_some_eq_heckeMatrix]

open _root_.ModularForm in
theorem heckeSlashSum_eq_heckeT (k : ℤ) (ℓ : ℕ) [NeZero ℓ] (f : ℍ → ℂ) :
    heckeSlashSum k ℓ f = heckeT k ℓ f := by
  rw [heckeSlashSum, heckeT_eq_heckeU_add, ← heckeUSlashSum_eq_heckeU, heckeUSlashSum,
    Fintype.sum_option, repGL_none_eq_heckeDiagMatrix, add_comm]

end WcPort.HeckeAnalytic
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort"
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort"

namespace WcPort
open UpperHalfPlane
open scoped ModularForm MatrixGroups

def toALData {M q : ℕ} (W : _root_.ModularForm.AtkinLehnerDatum M q) : ModularCurve.ALData M q :=
  ⟨W.R, W.hM, W.a, W.b, W.bezout⟩

theorem alGL_toALData {M q : ℕ} [NeZero M] (W : _root_.ModularForm.AtkinLehnerDatum M q) :
    HeckeAnalytic.alGL (toALData W) = W.alGL := by
  apply Units.ext
  rfl

theorem alSlash_toALData {M q : ℕ} [NeZero M] (W : _root_.ModularForm.AtkinLehnerDatum M q) (k : ℤ) (f : ℍ → ℂ) :
    HeckeAnalytic.alSlash (toALData W) k f = _root_.ModularForm.alSlash W k f := by
  rw [HeckeAnalytic.alSlash, alGL_toALData]; rfl

theorem traceSlashSum_toALData {M q : ℕ} [NeZero M] [NeZero q] (W : _root_.ModularForm.AtkinLehnerDatum M q) (k : ℤ) (f : ℍ → ℂ) :
    HeckeAnalytic.traceSlashSum (toALData W) k f = f + _root_.ModularForm.heckeU k q (_root_.ModularForm.alSlash W k f) := by
  rw [HeckeAnalytic.traceSlashSum_def, HeckeAnalytic.heckeUSlashSum_eq_heckeU, alSlash_toALData]

end WcPort
p2m_reactivate "P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort"

theorem solution {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), SlashAction.map (2 : ℤ) γ f = f)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (hγ : γ ∈ (CongruenceSubgroup.Gamma0 W.R : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    SlashAction.map (2 : ℤ) γ (f + ModularForm.heckeU 2 q (ModularForm.alSlash W 2 f))
      = f + ModularForm.heckeU 2 q (ModularForm.alSlash W 2 f) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  rw [← WcPort.traceSlashSum_toALData]
  exact WcPort.HeckeAnalytic.traceSlashSum_slash (WcPort.toALData W) hq hf hγ

end S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0
end P2MW
export P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0 (solution)
