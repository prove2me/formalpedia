-- Prove2me | solution 1 for ModularForm.alSlash_slash_eq_self_of_mem_Gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/c52cc815-2a2c-5b82-9be9-40c0b92b5a30

import Mathlib
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_alSlash_slash_eq_self_of_mem_Gamma0

open Matrix UpperHalfPlane CongruenceSubgroup
p2m_open_scoped "MatrixGroups ModularForm P2MW.S_ModularForm_alSlash_slash_eq_self_of_mem_Gamma0.ModularForm Manifold"

noncomputable section

namespace ModularForm
p2m_export "ModularForm" "smul_slash slash_apply ext smul_apply AtkinLehnerDatum AtkinLehnerDatum.sqUnitSL_coe AtkinLehnerDatum.alGL_coe alSlash"
p2m_open "ModularForm"

namespace AtkinLehnerDatum
p2m_export "ModularForm.AtkinLehnerDatum" "hM_int q_pos mat mat_sq sqUnitSL sqUnitSL_coe sqUnitSL_mem alGL alGL_coe alGLQ alGLQ_map_castHom hM b bezout R a"
p2m_open "ModularForm.AtkinLehnerDatum"

variable {M q : ℕ} (W : AtkinLehnerDatum M q)

private theorem _root_.ModularForm.AtkinLehnerDatum.mat_mul_normalizes (α β c δ : ℤ)
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

p2m_export "ModularForm.AtkinLehnerDatum" "mat_mul_normalizes"

theorem nonempty_of_prime_of_dvd_of_not_sq_dvd' (hq : q.Prime) (hqM : q ∣ M)
    (hsq : ¬ q ^ 2 ∣ M) : Nonempty (AtkinLehnerDatum M q) := by
  obtain ⟨R, hR⟩ := hqM

  have hqR : ¬ q ∣ R := by
    rintro ⟨t, rfl⟩
    exact hsq ⟨t, by rw [hR]; ring⟩

  have hqR' : ¬ (q : ℤ) ∣ (R : ℤ) := by exact_mod_cast hqR
  have hcop : IsCoprime (q : ℤ) (R : ℤ) :=
    (Nat.prime_iff_prime_int.mp hq).coprime_iff_not_dvd.mpr hqR'
  obtain ⟨u, v, huv⟩ := hcop
  exact ⟨⟨R, hR, u, -v, by linear_combination huv⟩⟩

theorem isEmpty_four_two : IsEmpty (AtkinLehnerDatum 4 2) := by
  constructor
  rintro ⟨R, hM, a, b, hbez⟩

  have hR : R = 2 := by omega
  subst hR

  omega

end AtkinLehnerDatum

p2m_open "ModularForm.AtkinLehnerDatum P2MW.S_ModularForm_alSlash_slash_eq_self_of_mem_Gamma0.ModularForm.AtkinLehnerDatum OnePoint"

variable {M q : ℕ} (W : AtkinLehnerDatum M q)

lemma isCusp_smul_of_rat' {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) {g : GL (Fin 2) ℝ}
    (gQ : GL (Fin 2) ℚ) (hg : gQ.map (Rat.castHom ℝ) = g) : IsCusp (g • c) 𝒮ℒ := by
  subst hg
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  refine ⟨gQ • c₀, ?_⟩
  rw [← Rat.coe_castHom, OnePoint.map_smul]

lemma isCusp_alGL_smul [NeZero M] {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsCusp (W.alGL • c) ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  exact isCusp_smul_of_rat' hc W.alGLQ W.alGLQ_map_castHom

private lemma mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

private lemma map_int_mul_eq (A P : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * P).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

lemma exists_cocycle_al [NeZero M] {g : SL(2, ℤ)} (hg : g ∈ Gamma0 M) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 M ∧
      W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ g
        = Matrix.SpecialLinearGroup.mapGL ℝ δ * W.alGL := by

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
    show (W.alGL : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = ((Matrix.SpecialLinearGroup.mapGL ℝ (⟨_, hdetδ⟩ : SL(2, ℤ)) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) * (W.alGL : Matrix (Fin 2) (Fin 2) ℝ)
    rw [AtkinLehnerDatum.alGL_coe, mapGL_coe_eq, mapGL_coe_eq, ← map_int_mul_eq, ← map_int_mul_eq]
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
  calc (f ∣[k] W.alGL) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g)
      = f ∣[k] (W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ g) := by
        rw [SlashAction.slash_mul]
    _ = f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ δ * W.alGL) := by rw [hcocycle]
    _ = (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ δ) ∣[k] W.alGL := by
        rw [SlashAction.slash_mul]
    _ = f ∣[k] W.alGL := by
        rw [hf (Matrix.SpecialLinearGroup.mapGL ℝ δ) (Subgroup.mem_map.mpr ⟨δ, hδ, rfl⟩)]

lemma alSlash_mdiff {k : ℤ} [NeZero M] {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (alSlash W k f) :=
  hf.slash k (W.alGL)

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
    W.alGL * W.alGL = scalarGL q W.q_pos * Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (W.alGL : Matrix (Fin 2) (Fin 2) ℝ) * (W.alGL : Matrix (Fin 2) (Fin 2) ℝ)
      = (scalarGL q W.q_pos : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ)
  rw [AtkinLehnerDatum.alGL_coe, scalarGL_coe, mapGL_coe_eq, AtkinLehnerDatum.sqUnitSL_coe, ← map_int_mul_eq, W.mat_sq]

  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.natCast_apply]

theorem alSlash_alSlash (k : ℤ) [NeZero M] {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) :
    alSlash W k (alSlash W k f) = ((q : ℂ) ^ (k - 2)) • f := by

  have hfu : f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL) = f :=
    hf _ (Subgroup.mem_map.mpr ⟨W.sqUnitSL, W.sqUnitSL_mem, rfl⟩)
  calc alSlash W k (alSlash W k f)
      = f ∣[k] (W.alGL * W.alGL) := by
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

end ModularForm
p2m_reactivate "P2MW.S_ModularForm_alSlash_slash_eq_self_of_mem_Gamma0.ModularForm"

end
p2m_reactivate "P2MW.S_ModularForm_alSlash_slash_eq_self_of_mem_Gamma0.ModularForm"

theorem solution {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), SlashAction.map k γ f = f)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (hγ : γ ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    SlashAction.map k γ (ModularForm.alSlash W k f) = ModularForm.alSlash W k f :=
  ModularForm.alSlash_slash W hf hγ

end S_ModularForm_alSlash_slash_eq_self_of_mem_Gamma0
end P2MW
export P2MW.S_ModularForm_alSlash_slash_eq_self_of_mem_Gamma0 (solution)
