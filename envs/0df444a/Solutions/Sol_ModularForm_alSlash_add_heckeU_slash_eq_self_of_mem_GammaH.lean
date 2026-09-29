-- Prove2me | solution 1 for ModularForm.alSlash_add_heckeU_slash_eq_self_of_mem_GammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/f3b554ce-ef6e-5c80-9ba4-dab9cf5be3b6

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_alSlash_add_heckeU_slash_eq_self_of_mem_GammaH

set_option autoImplicit false

noncomputable section

open Matrix CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace AlTrH

variable {M p : ℕ} (W : ModularForm.AtkinLehnerDatum M p)

def repMat : Option (Fin p) → Matrix (Fin 2) (Fin 2) ℤ
  | none => W.mat
  | some j => !![1, (j : ℤ); 0, (p : ℤ)]

@[scoped simp] lemma repMat_none : repMat W none = W.mat := rfl

@[scoped simp] lemma repMat_some (j : Fin p) : repMat W (some j) = !![1, (j : ℤ); 0, (p : ℤ)] := rfl

lemma not_dvd_b (hp : 1 < p) : ¬ (p : ℤ) ∣ W.b := by
  intro hdvd
  have h1 : (p : ℤ) ∣ 1 := by
    have h2 : (p : ℤ) ∣ (p : ℤ) * W.a - (W.R : ℤ) * W.b :=
      dvd_sub (Dvd.intro _ rfl) (hdvd.mul_left _)
    rwa [W.bezout] at h2
  have := Int.le_of_dvd one_pos h1
  omega

lemma not_dvd_R (hp : 1 < p) : ¬ (p : ℤ) ∣ (W.R : ℤ) := by
  intro hdvd
  have h1 : (p : ℤ) ∣ 1 := by
    have h2 : (p : ℤ) ∣ (p : ℤ) * W.a - (W.R : ℤ) * W.b :=
      dvd_sub (Dvd.intro _ rfl) (hdvd.mul_right _)
    rwa [W.bezout] at h2
  have := Int.le_of_dvd one_pos h1
  omega

lemma repMat_unique (hp : 1 < p) {E : Matrix (Fin 2) (Fin 2) ℤ}
    {i i' : Option (Fin p)} (h : repMat W i' = E * repMat W i) : i' = i := by
  cases i with
  | none =>
    cases i' with
    | none => rfl
    | some j' =>
      exfalso
      rw [repMat_some, repMat_none, ModularForm.AtkinLehnerDatum.mat, Matrix.eta_fin_two E,
        Matrix.mul_fin_two] at h
      have h00 : (1 : ℤ) = E 0 0 * ((p : ℤ) * W.a) + E 0 1 * ((p : ℤ) * (W.R : ℤ)) :=
        congrFun (congrFun h 0) 0
      have hdvd : (p : ℤ) ∣ 1 :=
        ⟨E 0 0 * W.a + E 0 1 * (W.R : ℤ), by linear_combination h00⟩
      have := Int.le_of_dvd one_pos hdvd
      omega
  | some j =>
    cases i' with
    | none =>
      exfalso
      rw [repMat_some, repMat_none, ModularForm.AtkinLehnerDatum.mat, Matrix.eta_fin_two E,
        Matrix.mul_fin_two] at h
      have h00 : (p : ℤ) * W.a = E 0 0 * 1 + E 0 1 * 0 := congrFun (congrFun h 0) 0
      have h01 : W.b = E 0 0 * (j : ℤ) + E 0 1 * (p : ℤ) := congrFun (congrFun h 0) 1
      exact not_dvd_b W hp ⟨W.a * (j : ℤ) + E 0 1, by linear_combination h01 - (j : ℤ) * h00⟩
    | some j' =>
      rw [repMat_some, repMat_some, Matrix.eta_fin_two E, Matrix.mul_fin_two] at h
      have h00 : (1 : ℤ) = E 0 0 * 1 + E 0 1 * 0 := congrFun (congrFun h 0) 0
      have h01 : (j' : ℤ) = E 0 0 * (j : ℤ) + E 0 1 * (p : ℤ) := congrFun (congrFun h 0) 1
      have hE : E 0 0 = 1 := by linear_combination -h00
      rw [hE, one_mul] at h01
      have hcast : ((j' : ℕ) : ZMod p) = ((j : ℕ) : ZMod p) := by
        have := congrArg (Int.cast : ℤ → ZMod p) h01
        push_cast at this
        simpa using this
      have hval : (j' : ℕ) = (j : ℕ) := by
        have hj := ZMod.val_cast_of_lt j.isLt
        have hj' := ZMod.val_cast_of_lt j'.isLt
        rw [← hj, ← hj', hcast]
      exact congrArg some (Fin.ext hval)

lemma exists_fin_dvd_sub_mul (hp : p.Prime) {x : ℤ} (t : ℤ) (hx : ¬ (p : ℤ) ∣ x) :
    ∃ j' : Fin p, (p : ℤ) ∣ t - x * (j' : ℤ) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hppos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hcop : IsCoprime (p : ℤ) x :=
    (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hx
  obtain ⟨u, v, huv⟩ := hcop
  have hmod := Int.emod_add_mul_ediv (v * t) (p : ℤ)
  have hnonneg : 0 ≤ (v * t) % (p : ℤ) := Int.emod_nonneg _ hp0
  have hlt : (v * t) % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos _ hppos
  have hcoe : ((((v * t) % (p : ℤ)).toNat : ℕ) : ℤ) = (v * t) % (p : ℤ) :=
    Int.toNat_of_nonneg hnonneg
  refine ⟨⟨((v * t) % (p : ℤ)).toNat, by omega⟩, ⟨t * u + x * ((v * t) / (p : ℤ)), ?_⟩⟩
  show t - x * ((((v * t) % (p : ℤ)).toNat : ℕ) : ℤ) = (p : ℤ) * (t * u + x * ((v * t) / (p : ℤ)))
  rw [hcoe]
  linear_combination (-t) * huv + (-x) * hmod

theorem mat_mul_normalizes (α β c δ : ℤ)
    (hdet : α * δ - β * ((p : ℤ) * (W.R : ℤ) * c) = 1) :
    ∃ x y s t : ℤ, x * t - y * ((p : ℤ) * (W.R : ℤ) * s) = 1 ∧
      t = -((W.R : ℤ) * W.b) * (α + (p : ℤ) * c) + W.a * ((p : ℤ) * (W.R : ℤ) * β + (p : ℤ) * δ) ∧
      W.mat * !![α, β; (p : ℤ) * (W.R : ℤ) * c, δ]
        = !![x, y; (p : ℤ) * (W.R : ℤ) * s, t] * W.mat := by
  refine ⟨(p : ℤ) * W.a * α + W.b * ((p : ℤ) * (W.R : ℤ)) * c
        - (W.R : ℤ) * ((p : ℤ) * W.a * β + W.b * δ),
      -(W.a * α * W.b) - W.b ^ 2 * (W.R : ℤ) * c + (p : ℤ) * W.a ^ 2 * β + W.a * W.b * δ,
      α + (p : ℤ) * c - (W.R : ℤ) * β - δ,
      -((W.R : ℤ) * W.b) * (α + (p : ℤ) * c) + W.a * ((p : ℤ) * (W.R : ℤ) * β + (p : ℤ) * δ),
      ?_, rfl, ?_⟩
  · linear_combination ((p : ℤ) * W.a - (W.R : ℤ) * W.b) ^ 2 * hdet
      + ((p : ℤ) * W.a - (W.R : ℤ) * W.b + 1) * W.bezout
  · rw [ModularForm.AtkinLehnerDatum.mat, Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · show (p : ℤ) * W.a * α + W.b * ((p : ℤ) * (W.R : ℤ) * c)
        = ((p : ℤ) * W.a * α + W.b * ((p : ℤ) * (W.R : ℤ)) * c
            - (W.R : ℤ) * ((p : ℤ) * W.a * β + W.b * δ)) * ((p : ℤ) * W.a)
          + (-(W.a * α * W.b) - W.b ^ 2 * (W.R : ℤ) * c + (p : ℤ) * W.a ^ 2 * β
              + W.a * W.b * δ) * ((p : ℤ) * (W.R : ℤ))
      linear_combination
        (-((W.R : ℤ) * W.b * c * (p : ℤ) + W.a * α * (p : ℤ))) * W.bezout
    · show (p : ℤ) * W.a * β + W.b * δ
        = ((p : ℤ) * W.a * α + W.b * ((p : ℤ) * (W.R : ℤ)) * c
            - (W.R : ℤ) * ((p : ℤ) * W.a * β + W.b * δ)) * W.b
          + (-(W.a * α * W.b) - W.b ^ 2 * (W.R : ℤ) * c + (p : ℤ) * W.a ^ 2 * β
              + W.a * W.b * δ) * (p : ℤ)
      linear_combination (-(W.a * β * (p : ℤ) + W.b * δ)) * W.bezout
    · show (p : ℤ) * (W.R : ℤ) * α + (p : ℤ) * ((p : ℤ) * (W.R : ℤ) * c)
        = (p : ℤ) * (W.R : ℤ) * (α + (p : ℤ) * c - (W.R : ℤ) * β - δ) * ((p : ℤ) * W.a)
          + (-((W.R : ℤ) * W.b) * (α + (p : ℤ) * c)
              + W.a * ((p : ℤ) * (W.R : ℤ) * β + (p : ℤ) * δ)) * ((p : ℤ) * (W.R : ℤ))
      linear_combination
        (-((W.R : ℤ) * α * (p : ℤ) + (W.R : ℤ) * c * (p : ℤ) ^ 2)) * W.bezout
    · show (p : ℤ) * (W.R : ℤ) * β + (p : ℤ) * δ
        = (p : ℤ) * (W.R : ℤ) * (α + (p : ℤ) * c - (W.R : ℤ) * β - δ) * W.b
          + (-((W.R : ℤ) * W.b) * (α + (p : ℤ) * c)
              + W.a * ((p : ℤ) * (W.R : ℤ) * β + (p : ℤ) * δ)) * (p : ℤ)
      linear_combination (-((W.R : ℤ) * β * (p : ℤ) + δ * (p : ℤ))) * W.bezout

lemma natCast_R_eq_zero : ((W.R : ℕ) : ZMod W.R) = 0 := ZMod.natCast_self W.R

lemma p_mul_a_eq_one : ((p : ℕ) : ZMod W.R) * ((W.a : ℤ) : ZMod W.R) = 1 := by
  have := congrArg (Int.cast : ℤ → ZMod W.R) W.bezout
  push_cast at this
  rw [ZMod.natCast_self, zero_mul, sub_zero] at this
  exact this

theorem exists_cocycle (hp : p.Prime) {g : SL(2, ℤ)} (hg : g ∈ Gamma0 W.R) (i : Option (Fin p)) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 M ∧
      (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod W.R)
        = (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod W.R) ∧
      ∃ i' : Option (Fin p),
        repMat W i * (g : Matrix (Fin 2) (Fin 2) ℤ) = (δ : Matrix (Fin 2) (Fin 2) ℤ) * repMat W i' := by
  have hp1 : 1 < p := hp.one_lt
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
  have hmemM : ∀ x : ℤ, (((p : ℤ) * (W.R : ℤ) * x : ℤ) : ZMod M) = 0 := by
    intro x
    rw [← W.hM_int]
    push_cast
    simp
  have hR0 := natCast_R_eq_zero W
  have hpa := p_mul_a_eq_one W
  cases i with
  | none =>
    by_cases hqc : (p : ℤ) ∣ c
    ·
      obtain ⟨c', rfl⟩ := hqc
      obtain ⟨x, y, s, t, hdet1, ht, hmat⟩ := mat_mul_normalizes W α β c' d
        (by linear_combination hdet')
      have hdetδ : Matrix.det !![x, y; (p : ℤ) * (W.R : ℤ) * s, t] = 1 := by
        rw [Matrix.det_fin_two_of]; linear_combination hdet1
      refine ⟨⟨_, hdetδ⟩, ?_, ?_, none, ?_⟩
      · rw [Gamma0_mem]; exact hmemM s
      · show ((t : ℤ) : ZMod W.R) = ((d : ℤ) : ZMod W.R)
        rw [ht]
        push_cast
        rw [hR0]
        linear_combination ((d : ℤ) : ZMod W.R) * hpa
      · rw [repMat_none, hgmat,
          show (W.R : ℤ) * ((p : ℤ) * c') = (p : ℤ) * (W.R : ℤ) * c' by ring]
        exact hmat
    ·
      have hqRc : ¬ (p : ℤ) ∣ (W.R : ℤ) * c :=
        fun hdvd => hqc ((Int.Prime.dvd_mul' hp hdvd).resolve_left (not_dvd_R W hp1))
      obtain ⟨j', hj'⟩ := exists_fin_dvd_sub_mul hp d hqRc
      obtain ⟨e, he⟩ := hj'
      have hdetδ : Matrix.det
          !![(W.R : ℤ) * W.b * c + (p : ℤ) * W.a * α, -(W.a * α * (j' : ℤ)) + W.a * β + W.b * e;
             (p : ℤ) * (W.R : ℤ) * (α + c), -((W.R : ℤ) * α * (j' : ℤ)) + (W.R : ℤ) * β
               + (p : ℤ) * e] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination ((p : ℤ) * W.a - (W.R : ℤ) * W.b) * hdet' + W.bezout
          + ((W.R : ℤ) * α * W.b - W.a * α * (p : ℤ)) * he
      refine ⟨⟨_, hdetδ⟩, ?_, ?_, some j', ?_⟩
      · rw [Gamma0_mem]; exact hmemM (α + c)
      · show ((-((W.R : ℤ) * α * (j' : ℤ)) + (W.R : ℤ) * β + (p : ℤ) * e : ℤ) : ZMod W.R)
          = ((d : ℤ) : ZMod W.R)
        have hec := congrArg (Int.cast : ℤ → ZMod W.R) he
        push_cast at hec ⊢
        rw [hR0] at hec ⊢
        linear_combination -hec
      · rw [repMat_none, repMat_some, hgmat]
        show W.mat * _ = _
        rw [ModularForm.AtkinLehnerDatum.mat, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show (p : ℤ) * W.a * α + W.b * ((W.R : ℤ) * c)
            = ((W.R : ℤ) * W.b * c + (p : ℤ) * W.a * α) * 1
              + (-(W.a * α * (j' : ℤ)) + W.a * β + W.b * e) * 0
          ring
        · show (p : ℤ) * W.a * β + W.b * d
            = ((W.R : ℤ) * W.b * c + (p : ℤ) * W.a * α) * (j' : ℤ)
              + (-(W.a * α * (j' : ℤ)) + W.a * β + W.b * e) * (p : ℤ)
          linear_combination W.b * he
        · show (p : ℤ) * (W.R : ℤ) * α + (p : ℤ) * ((W.R : ℤ) * c)
            = (p : ℤ) * (W.R : ℤ) * (α + c) * 1
              + (-((W.R : ℤ) * α * (j' : ℤ)) + (W.R : ℤ) * β + (p : ℤ) * e) * 0
          ring
        · show (p : ℤ) * (W.R : ℤ) * β + (p : ℤ) * d
            = (p : ℤ) * (W.R : ℤ) * (α + c) * (j' : ℤ)
              + (-((W.R : ℤ) * α * (j' : ℤ)) + (W.R : ℤ) * β + (p : ℤ) * e) * (p : ℤ)
          linear_combination (p : ℤ) * he
  | some j =>
    by_cases hpiv : (p : ℤ) ∣ (α + (j : ℤ) * ((W.R : ℤ) * c))
    ·
      obtain ⟨e, he⟩ := hpiv
      have hdetδ : Matrix.det
          !![-((W.R : ℤ) * β) - (W.R : ℤ) * d * (j : ℤ) + (p : ℤ) * e,
             W.a * β + W.a * d * (j : ℤ) - W.b * e;
             (p : ℤ) * (W.R : ℤ) * (c - d), -((W.R : ℤ) * W.b * c) + (p : ℤ) * W.a * d] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdet'
          + (-((W.R : ℤ) * β * c) - (W.R : ℤ) * c * d * (j : ℤ) + d * e * (p : ℤ)) * W.bezout
          + (-d) * he
      refine ⟨⟨_, hdetδ⟩, ?_, ?_, none, ?_⟩
      · rw [Gamma0_mem]; exact hmemM (c - d)
      · show ((-((W.R : ℤ) * W.b * c) + (p : ℤ) * W.a * d : ℤ) : ZMod W.R) = ((d : ℤ) : ZMod W.R)
        push_cast
        rw [hR0]
        linear_combination ((d : ℤ) : ZMod W.R) * hpa
      · rw [repMat_some, repMat_none, hgmat]
        show _ = _ * W.mat
        rw [ModularForm.AtkinLehnerDatum.mat, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show 1 * α + (j : ℤ) * ((W.R : ℤ) * c)
            = (-((W.R : ℤ) * β) - (W.R : ℤ) * d * (j : ℤ) + (p : ℤ) * e) * ((p : ℤ) * W.a)
              + (W.a * β + W.a * d * (j : ℤ) - W.b * e) * ((p : ℤ) * (W.R : ℤ))
          linear_combination he + (-((p : ℤ) * e)) * W.bezout
        · show 1 * β + (j : ℤ) * d
            = (-((W.R : ℤ) * β) - (W.R : ℤ) * d * (j : ℤ) + (p : ℤ) * e) * W.b
              + (W.a * β + W.a * d * (j : ℤ) - W.b * e) * (p : ℤ)
          linear_combination (-(β + d * (j : ℤ))) * W.bezout
        · show 0 * α + (p : ℤ) * ((W.R : ℤ) * c)
            = (p : ℤ) * (W.R : ℤ) * (c - d) * ((p : ℤ) * W.a)
              + (-((W.R : ℤ) * W.b * c) + (p : ℤ) * W.a * d) * ((p : ℤ) * (W.R : ℤ))
          linear_combination (-((p : ℤ) * (W.R : ℤ) * c)) * W.bezout
        · show 0 * β + (p : ℤ) * d
            = (p : ℤ) * (W.R : ℤ) * (c - d) * W.b
              + (-((W.R : ℤ) * W.b * c) + (p : ℤ) * W.a * d) * (p : ℤ)
          linear_combination (-((p : ℤ) * d)) * W.bezout
    ·
      obtain ⟨j', hj'⟩ := exists_fin_dvd_sub_mul hp (β + (j : ℤ) * d) hpiv
      obtain ⟨e, he⟩ := hj'
      have hdetδ : Matrix.det
          !![α + (j : ℤ) * ((W.R : ℤ) * c), e;
             (p : ℤ) * (W.R : ℤ) * c, d - (W.R : ℤ) * c * (j' : ℤ)] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdet' + ((W.R : ℤ) * c) * he
      refine ⟨⟨_, hdetδ⟩, ?_, ?_, some j', ?_⟩
      · rw [Gamma0_mem]; exact hmemM c
      · show ((d - (W.R : ℤ) * c * (j' : ℤ) : ℤ) : ZMod W.R) = ((d : ℤ) : ZMod W.R)
        push_cast
        rw [hR0]
        ring
      · rw [repMat_some, repMat_some, hgmat]
        rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show 1 * α + (j : ℤ) * ((W.R : ℤ) * c)
            = (α + (j : ℤ) * ((W.R : ℤ) * c)) * 1 + e * 0
          ring
        · show 1 * β + (j : ℤ) * d
            = (α + (j : ℤ) * ((W.R : ℤ) * c)) * (j' : ℤ) + e * (p : ℤ)
          linear_combination he
        · show 0 * α + (p : ℤ) * ((W.R : ℤ) * c)
            = (p : ℤ) * (W.R : ℤ) * c * 1 + (d - (W.R : ℤ) * c * (j' : ℤ)) * 0
          ring
        · show 0 * β + (p : ℤ) * d
            = (p : ℤ) * (W.R : ℤ) * c * (j' : ℤ) + (d - (W.R : ℤ) * c * (j' : ℤ)) * (p : ℤ)
          ring

section GLtransfer

variable [NeZero M]

def repGL : Option (Fin p) → GL (Fin 2) ℝ
  | none => W.alGL
  | some j => ModularForm.heckeMatrix p (j : ℕ)

@[scoped simp] lemma repGL_none : repGL W none = W.alGL := rfl

@[scoped simp] lemma repGL_some (j : Fin p) : repGL W (some j) = ModularForm.heckeMatrix p (j : ℕ) := rfl

lemma mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

lemma map_int_mul_eq (A P : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * P).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

lemma repGL_coe (hp : p ≠ 0) (i : Option (Fin p)) :
    (repGL W i : Matrix (Fin 2) (Fin 2) ℝ) = (repMat W i).map (algebraMap ℤ ℝ) := by
  cases i with
  | none => exact W.alGL_coe
  | some j =>
    rw [repGL_some, repMat_some, ModularForm.val_heckeMatrix hp]
    refine Matrix.ext fun x y => ?_
    fin_cases x <;> fin_cases y <;> simp

lemma repGL_cocycle_of_int (hp : p ≠ 0) {g δ : SL(2, ℤ)} {i i' : Option (Fin p)}
    (hint : repMat W i * (g : Matrix (Fin 2) (Fin 2) ℤ) = (δ : Matrix (Fin 2) (Fin 2) ℤ) * repMat W i') :
    repGL W i * Matrix.SpecialLinearGroup.mapGL ℝ g
      = Matrix.SpecialLinearGroup.mapGL ℝ δ * repGL W i' := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (repGL W i : Matrix (Fin 2) (Fin 2) ℝ) *
      ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
    = ((Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
      (repGL W i' : Matrix (Fin 2) (Fin 2) ℝ)
  rw [repGL_coe W hp, repGL_coe W hp, mapGL_coe_eq, mapGL_coe_eq, ← map_int_mul_eq,
    ← map_int_mul_eq, hint]

lemma sum_slash_repGL (f : UpperHalfPlane → ℂ) :
    ∑ i : Option (Fin p), f ∣[(2 : ℤ)] repGL W i
      = ModularForm.alSlash W 2 f + ModularForm.heckeU 2 p f := by
  rw [Fintype.sum_option, repGL_none, ModularForm.alSlash_def, ModularForm.heckeU_def,
    Finset.sum_range (fun j => f ∣[(2 : ℤ)] ModularForm.heckeMatrix p j)]
  rfl

end GLtransfer

lemma mem_GammaH_of_congr (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 M)
    {u : (ZMod M)ˣ} (hu : u ∈ H)
    (hcongr : (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod W.R)
      = (ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u : ZMod W.R)) :
    δ ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨hδ, ?_⟩
  set v : (ZMod M)ˣ := CohCarrier.gamma0Units M ⟨δ, hδ⟩ with hv
  have hmap : ZMod.unitsMap (Dvd.intro_left p W.hM.symm) v
      = ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u := by
    ext
    rw [← hcongr, ZMod.unitsMap_val, hv, CohCarrier.val_gamma0Units]
    show (((((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M)).cast : ZMod W.R) = _
    rw [ZMod.cast_intCast (Dvd.intro_left p W.hM.symm)]
  have hker : v * u⁻¹ ∈ H := hHp _ (by rw [map_mul, map_inv, hmap, mul_inv_cancel])
  simpa using H.mul_mem hker hu

theorem main [NeZero M] (hp : p.Prime) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[(2 : ℤ)] γ = f)
    (g : SL(2, ℤ)) (hg : g ∈ Gamma0 W.R)
    (hgH : ∃ u ∈ H, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = CohCarrier.gamma0Units W.R ⟨g, hg⟩) :
    (ModularForm.alSlash W 2 f + ModularForm.heckeU 2 p f) ∣[(2 : ℤ)]
        (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ)
      = ModularForm.alSlash W 2 f + ModularForm.heckeU 2 p f := by
  have hp0 : p ≠ 0 := hp.ne_zero
  obtain ⟨u, hu, hug⟩ := hgH

  choose δ hδ hcong m hm using fun i => exists_cocycle W hp hg i

  have hδH : ∀ i, δ i ∈ CohCarrier.GammaH M H := by
    intro i
    refine mem_GammaH_of_congr W H hHp (hδ i) hu ?_
    rw [hcong i, hug, CohCarrier.val_gamma0Units]
    rfl

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
    have hcomb : repMat W i₁ =
        ((δ i₁ * (δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat W i₂ := by
      have step : repMat W i₁ * (g : Matrix (Fin 2) (Fin 2) ℤ) =
          (((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
            (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
            (repMat W i₂ * (g : Matrix (Fin 2) (Fin 2) ℤ)) := by
        calc repMat W i₁ * (g : Matrix (Fin 2) (Fin 2) ℤ)
            = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat W (m i₂) := h₁
          _ = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                ((((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                  (((δ i₂ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * repMat W (m i₂))) := by
              rw [← mul_assoc (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), hδ₂, one_mul]
          _ = ((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                ((((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                  (repMat W i₂ * (g : Matrix (Fin 2) (Fin 2) ℤ))) := by rw [h₂]
          _ = (((δ i₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
                (((δ i₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
                (repMat W i₂ * (g : Matrix (Fin 2) (Fin 2) ℤ)) := by
              simp only [mul_assoc]
      have := congrArg (· * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) step
      simp only [mul_assoc, hg_inv, mul_one] at this
      rw [this, Matrix.SpecialLinearGroup.coe_mul, mul_assoc]
    exact repMat_unique W hp.one_lt hcomb
  have hbij : Function.Bijective m := Finite.injective_iff_bijective.mp hinj
  have hmGL : ∀ i, repGL W i * Matrix.SpecialLinearGroup.mapGL ℝ g =
      Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * repGL W (m i) :=
    fun i => repGL_cocycle_of_int W hp0 (hm i)
  rw [← sum_slash_repGL W f]
  calc (∑ i : Option (Fin p), f ∣[(2 : ℤ)] repGL W i) ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ g)
      = ∑ i : Option (Fin p), (f ∣[(2 : ℤ)] repGL W i) ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ g) := by
        rw [SlashAction.sum_slash]
    _ = ∑ i : Option (Fin p), f ∣[(2 : ℤ)] (repGL W i * Matrix.SpecialLinearGroup.mapGL ℝ g) := by
        simp_rw [SlashAction.slash_mul]
    _ = ∑ i : Option (Fin p), f ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (δ i) * repGL W (m i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hmGL i]
    _ = ∑ i : Option (Fin p), (f ∣[(2 : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ (δ i)) ∣[(2 : ℤ)]
          repGL W (m i) := by
        simp_rw [SlashAction.slash_mul]
    _ = ∑ i : Option (Fin p), f ∣[(2 : ℤ)] repGL W (m i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hf _ (Subgroup.mem_map.mpr ⟨δ i, hδH i, rfl⟩)]
    _ = ∑ i : Option (Fin p), f ∣[(2 : ℤ)] repGL W i :=
        hbij.sum_comp fun i => f ∣[(2 : ℤ)] repGL W i

end AlTrH
p2m_reactivate "P2MW.S_ModularForm_alSlash_add_heckeU_slash_eq_self_of_mem_GammaH.AlTrH"

end
p2m_reactivate "P2MW.S_ModularForm_alSlash_add_heckeU_slash_eq_self_of_mem_GammaH.AlTrH"

theorem solution
    {M p : ℕ} [NeZero M] (hp : p.Prime) (W : ModularForm.AtkinLehnerDatum M p)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)),
      SlashAction.map (2 : ℤ) γ f = f)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hg : g ∈ CongruenceSubgroup.Gamma0 W.R)
    (hgH : ∃ u ∈ H,
      ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = CohCarrier.gamma0Units W.R ⟨g, hg⟩) :
    SlashAction.map (2 : ℤ) (Matrix.SpecialLinearGroup.mapGL ℝ g)
        (ModularForm.alSlash W 2 f + ModularForm.heckeU 2 p f) =
      ModularForm.alSlash W 2 f + ModularForm.heckeU 2 p f :=
  AlTrH.main W hp H hHp hf g hg hgH

end S_ModularForm_alSlash_add_heckeU_slash_eq_self_of_mem_GammaH
end P2MW
export P2MW.S_ModularForm_alSlash_add_heckeU_slash_eq_self_of_mem_GammaH (solution)
