-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.firstRatioCoeff_flat_of_le_of_flat_of_casimir_relations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a7ff462e-85de-5321-812e-8294b883478d

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow
import Theorems.Thm_Matrix_exists_const_forall_norm_le_mul_of_norm_sum_pow_smul_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_firstRatioCoeff_flat_of_le_of_flat_of_casimir_relations

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

namespace WsB
namespace FU

def ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v : InfinitePlace ℚ =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

def realM (e : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) := e.map ofRealHom

theorem archRealMat3_eq (e : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 e = archMatrixInclN (Fin 3) ℚ (realM e) := rfl

theorem realM_mul (e f : Matrix (Fin 3) (Fin 3) ℝ) : realM (e * f) = realM e * realM f := Matrix.map_mul

theorem isUnit_archRealMat3 (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) :
    IsUnit (WhittakerBlock.archRealMat3 e) := by
  rw [archRealMat3_eq]
  have h0 : IsUnit (Matrix.of e) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)
  exact (h0.map (RingHom.mapMatrix ofRealHom)).map (archMatrixInclHomN (Fin 3) ℚ)

theorem val_lift (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) :
    ((WhittakerBlock.archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      WhittakerBlock.archRealMat3 e := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos (isUnit_archRealMat3 e h)]
  exact IsUnit.unit_spec _

theorem lift_mul (e f : Matrix (Fin 3) (Fin 3) ℝ) (he : e.det ≠ 0) (hf : f.det ≠ 0) :
    WhittakerBlock.archRealLift3 (e * f) = WhittakerBlock.archRealLift3 e * WhittakerBlock.archRealLift3 f := by
  have hef : (Matrix.of (e * f)).det ≠ 0 := by
    change (e * f).det ≠ 0
    rw [Matrix.det_mul]; exact mul_ne_zero he hf
  refine Units.ext ?_
  rw [Units.val_mul, val_lift _ hef, val_lift _ he, val_lift _ hf, archRealMat3_eq, archRealMat3_eq,
    archRealMat3_eq, ← archMatrixInclN_mul, ← realM_mul]

theorem torus_mul_a (y₁ y₂ α : ℝ) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (hα : 0 < α) :
    WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) *
      WhittakerBlock.archRealLift3 (fun i j => if i = j then ![α, 1, 1] i else 0) =
    WhittakerBlock.archRealLift3 (fun i j => if i = j then ![α * y₁ * y₂, y₂, 1] i else 0) := by
  have h1 : (Matrix.of fun i j : Fin 3 => if i = j then ![y₁ * y₂, y₂, 1] i else 0).det ≠ 0 := by
    rw [Matrix.det_fin_three]; simp [hy₁.ne', hy₂.ne']
  have h2 : (Matrix.of fun i j : Fin 3 => if i = j then ![α, 1, 1] i else 0).det ≠ 0 := by
    rw [Matrix.det_fin_three]; simp [hα.ne']
  have hprod : (Matrix.of fun i j : Fin 3 => if i = j then ![y₁ * y₂, y₂, 1] i else 0) *
      (Matrix.of fun i j : Fin 3 => if i = j then ![α, 1, 1] i else 0) =
      Matrix.of fun i j : Fin 3 => if i = j then ![α * y₁ * y₂, y₂, 1] i else 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  have := lift_mul _ _ h1 h2
  rw [hprod] at this
  exact this.symm

theorem rescale_expansion {n J : ℕ} (e : Fin n → ℂ) (c : Fin n → Fin J → ℂ) (lam : ℝ) (hlam : 0 < lam)
    (y : ℝ) (hy : 0 < y) :
    ∑ i : Fin n, ∑ j : Fin J,
        c i j * (((lam * y : ℝ) : ℂ) ^ e i * ((Real.log (lam * y) : ℝ) : ℂ) ^ (j : ℕ)) =
      ∑ i : Fin n, ∑ k : Fin J,
        (∑ m : Fin J, if (k : ℕ) ≤ (m : ℕ) then
            c i m * ((lam : ℝ) : ℂ) ^ e i * ((Real.log lam : ℝ) : ℂ) ^ ((m : ℕ) - (k : ℕ)) *
              (((m : ℕ).choose (k : ℕ) : ℕ) : ℂ)
          else 0) * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (k : ℕ)) := by
  classical
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpow : ((lam * y : ℝ) : ℂ) ^ e i = ((lam : ℝ) : ℂ) ^ e i * (y : ℂ) ^ e i := by
    rw [Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg hlam.le hy.le (e i)
  have hlog : ((Real.log (lam * y) : ℝ) : ℂ) = ((Real.log y : ℝ) : ℂ) + ((Real.log lam : ℝ) : ℂ) := by
    rw [Real.log_mul hlam.ne' hy.ne', add_comm]
    push_cast
    ring
  have hL : ∀ m : Fin J, c i m * (((lam * y : ℝ) : ℂ) ^ e i * ((Real.log (lam * y) : ℝ) : ℂ) ^ (m : ℕ)) =
      ∑ k : Fin J, (if (k : ℕ) ≤ (m : ℕ) then
          c i m * ((lam : ℝ) : ℂ) ^ e i * ((Real.log lam : ℝ) : ℂ) ^ ((m : ℕ) - (k : ℕ)) *
            (((m : ℕ).choose (k : ℕ) : ℕ) : ℂ)
        else 0) * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (k : ℕ)) := by
    intro m
    rw [hpow, hlog, add_pow]
    have hidx : ∀ f : ℕ → ℂ, ∑ k ∈ Finset.range ((m : ℕ) + 1), f k =
        ∑ k : Fin J, if (k : ℕ) ≤ (m : ℕ) then f k else 0 := by
      intro f
      rw [Fin.sum_univ_eq_sum_range (fun k => if k ≤ (m : ℕ) then f k else 0) J, ← Finset.sum_filter]
      have hfil : (Finset.range J).filter (fun k => k ≤ (m : ℕ)) = Finset.range ((m : ℕ) + 1) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range]
        have := m.2
        omega
      rw [hfil]
    rw [Finset.mul_sum, Finset.mul_sum, hidx]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) ≤ (m : ℕ)
    · simp only [if_pos hk]
      ring
    · simp only [if_neg hk]
      ring
  rw [Finset.sum_congr rfl fun m _ => hL m, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]

def Wfun (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
    NumberField.StandardAddChar.psiQ u g

def HasExpansion {n J : ℕ} (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (e : Fin n → ℂ) (θ : ℝ)
    (c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
    ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
    ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ u
        (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
      (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
    C * y₁ ^ θ

theorem coeff_rescale {n J : ℕ} (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (e : Fin n → ℂ) (he : Function.Injective e)
    (ρ δ : ℝ) (hδ : 0 < δ) (hre : ∀ i, (e i).re ≤ ρ)
    (c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hexp : HasExpansion u e (ρ + δ) c)
    (i : Fin n) (m : Fin J) (k : AdelicGL 3 (𝓞 ℚ) ℚ) (y₂ : ℝ) (hy₂ : 0 < y₂) (α : ℝ) (hα0 : 0 < α)
    (hα1 : α ≤ 1) :
    c i m y₂ (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![α, 1, 1] i else 0) * k) =
      ∑ j' : Fin J, if (m : ℕ) ≤ (j' : ℕ) then
        c i j' y₂ k * ((α : ℝ) : ℂ) ^ e i * ((Real.log α : ℝ) : ℂ) ^ ((j' : ℕ) - (m : ℕ)) *
          (((j' : ℕ).choose (m : ℕ) : ℕ) : ℂ)
        else 0 := by
  classical
  set a : AdelicGL 3 (𝓞 ℚ) ℚ := WhittakerBlock.archRealLift3 (fun i j => if i = j then ![α, 1, 1] i else 0)
    with ha
  set k' : AdelicGL 3 (𝓞 ℚ) ℚ := a * k with hk'

  set b : ℝ := max y₂ y₂⁻¹ with hb
  have hb1 : 1 ≤ b := by
    rcases le_or_gt 1 y₂ with h | h
    · exact le_trans h (le_max_left _ _)
    · exact le_trans (one_le_inv_iff₀.mpr ⟨hy₂, h.le⟩) (le_max_right _ _)
  have hyb1 : b⁻¹ ≤ y₂ := by
    rw [inv_le_comm₀ (lt_of_lt_of_le one_pos hb1) hy₂]; exact le_max_right _ _
  have hyb2 : y₂ ≤ b := le_max_left _ _
  obtain ⟨C₁, hC₁⟩ := hexp {k'} isCompact_singleton b hb1
  obtain ⟨C₂, hC₂⟩ := hexp {k} isCompact_singleton b hb1

  set D : Fin n → Fin J → ℂ := fun i mm => ∑ j' : Fin J, if (mm : ℕ) ≤ (j' : ℕ) then
      c i j' y₂ k * ((α : ℝ) : ℂ) ^ e i * ((Real.log α : ℝ) : ℂ) ^ ((j' : ℕ) - (mm : ℕ)) *
        (((j' : ℕ).choose (mm : ℕ) : ℕ) : ℂ) else 0 with hD

  set cc : Fin n × Fin J → ℂ := fun p => c p.1 p.2 y₂ k' - D p.1 p.2 with hcc
  set F : ℝ → ℂ := fun y => ∑ p : Fin n × Fin J, cc p * ((y : ℂ) ^ e p.1 * ((Real.log y : ℝ) : ℂ) ^ (p.2 : ℕ))
    with hF
  have hFeq : ∀ y : ℝ, 0 < y → y ≤ 1 →
      F y = (Wfun u (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![α * y * y₂, y₂, 1] i else 0) * k) -
              ∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((((α * y : ℝ)) : ℂ) ^ e i *
                ((Real.log (α * y) : ℝ) : ℂ) ^ (j : ℕ))) -
            (Wfun u (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * y₂, y₂, 1] i else 0) * k') -
              ∑ i : Fin n, ∑ j : Fin J, c i j y₂ k' * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))) := by
    intro y hy0 hy1
    have hW : Wfun u (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * y₂, y₂, 1] i else 0) * k') =
        Wfun u (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![α * y * y₂, y₂, 1] i else 0) * k) := by
      rw [hk', ← mul_assoc, ha, torus_mul_a y y₂ α hy0 hy₂ hα0]
    rw [hW, rescale_expansion e (fun i j => c i j y₂ k) α hα0 y hy0]
    simp only [hF, hcc, Fintype.sum_prod_type, sub_mul, Finset.sum_sub_distrib, hD]
    ring
  have hsel := LanglandsTunnell.CubicInduction.expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow
    (ι := Fin n × Fin J) (fun p => e p.1) (fun p => (p.2 : ℕ)) cc
    (by
      intro p q hpq
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext (he hpq.1) (Fin.ext hpq.2))
    (ρ + δ) F (fun _ => 0)
    (by intro y hy0 hy1; simp [hF])
    ⟨0, by intro y hy0 hy1; simp⟩
    ⟨C₂ * α ^ (ρ + δ) + C₁, by
      intro y hy0 hy1
      rw [hFeq y hy0 hy1]
      have h2 := hC₂ k (Set.mem_singleton k) y₂ hyb1 hyb2 (α * y) (mul_pos hα0 hy0)
        (by nlinarith)
      have h1 := hC₁ k' (Set.mem_singleton k') y₂ hyb1 hyb2 y hy0 hy1
      have hαy : (α * y) ^ (ρ + δ) = α ^ (ρ + δ) * y ^ (ρ + δ) := Real.mul_rpow hα0.le hy0.le
      have e1 : α * y * y₂ = (α * y) * y₂ := by ring
      calc ‖_‖ ≤ ‖Wfun u (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![α * y * y₂, y₂, 1] i else 0) * k) -
              ∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((((α * y : ℝ)) : ℂ) ^ e i *
                ((Real.log (α * y) : ℝ) : ℂ) ^ (j : ℕ))‖ +
            ‖Wfun u (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * y₂, y₂, 1] i else 0) * k') -
              ∑ i : Fin n, ∑ j : Fin J, c i j y₂ k' * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ :=
            norm_sub_le _ _
        _ ≤ C₂ * (α * y) ^ (ρ + δ) + C₁ * y ^ (ρ + δ) := add_le_add h2 h1
        _ = (C₂ * α ^ (ρ + δ) + C₁) * y ^ (ρ + δ) := by rw [hαy]; ring⟩
  have h0 := hsel (i, m) (lt_of_le_of_lt (hre i) (by linarith))
  simp only [hcc, sub_eq_zero] at h0
  rw [h0]

end WsB.FU

namespace WsB
namespace FU

theorem sum_ite_le_eq_sum_offset (J : ℕ) (j : Fin J) (g : ℕ → ℂ) :
    (∑ j' : Fin J, if (j : ℕ) ≤ (j' : ℕ) then g j' else 0) =
      ∑ s ∈ Finset.range (J - j), g ((j : ℕ) + s) := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun m => if (j : ℕ) ≤ m then g m else 0) J, ← Finset.sum_filter]
  have hfil : (Finset.range J).filter (fun m => (j : ℕ) ≤ m) = Finset.Ico (j : ℕ) J := by
    ext m; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hfil, Finset.sum_Ico_eq_sum_range]

theorem climb {n J : ℕ} (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (e : Fin n → ℂ) (he : Function.Injective e)
    (ρ δ : ℝ) (hδ : 0 < δ) (hre : ∀ i, (e i).re ≤ ρ)
    (c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hexp : HasExpansion u e (ρ + δ) c)
    (i : Fin n) (j : Fin J)
    (hflat : ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K,
      ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 → ‖c i j y₂ k‖ ≤ C * y₂ ^ (ρ + δ))
    (j' : Fin J) (hjj' : j ≤ j') :
    ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K,
      ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 → ‖c i j' y₂ k‖ ≤ C * y₂ ^ (ρ + δ) := by
  classical
  intro K hK

  set L : ℕ := J - (j : ℕ) with hL
  have hLpos : (j' : ℕ) - (j : ℕ) < L := by
    have := j'.2; have : (j : ℕ) ≤ (j' : ℕ) := hjj'; omega
  set α : Fin L → ℝ := fun t => Real.exp (-(t : ℝ)) with hα
  have hα0 : ∀ t, 0 < α t := fun t => Real.exp_pos _
  have hα1 : ∀ t, α t ≤ 1 := fun t => by
    show Real.exp (-(t : ℝ)) ≤ 1
    rw [Real.exp_le_one_iff]
    have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
    linarith
  have hlogα : ∀ t, Real.log (α t) = -(t : ℝ) := fun t => Real.log_exp _
  set x : Fin L → ℂ := fun t => ((-(t : ℝ) : ℝ) : ℂ) with hx
  have hxinj : Function.Injective x := by
    intro t t' h
    simp only [hx] at h
    have : ((t : ℕ) : ℝ) = ((t' : ℕ) : ℝ) := by
      have := congrArg Complex.re h; simpa using this
    exact Fin.ext (Nat.cast_injective this)
  obtain ⟨CV, hCV0, hV⟩ := Matrix.exists_const_forall_norm_le_mul_of_norm_sum_pow_smul_le L x hxinj

  set a : Fin L → AdelicGL 3 (𝓞 ℚ) ℚ := fun t =>
    WhittakerBlock.archRealLift3 (fun i j => if i = j then ![α t, 1, 1] i else 0) with ha
  set K' : Set (AdelicGL 3 (𝓞 ℚ) ℚ) := ⋃ t : Fin L, (fun k => a t * k) '' K with hK'
  have hK'c : IsCompact K' := isCompact_iUnion (fun t => hK.image (continuous_mul_left (a t)))
  obtain ⟨C', hC'⟩ := hflat K' hK'c
  set C'' : ℝ := max C' 0 with hC''
  have hC''0 : 0 ≤ C'' := le_max_right _ _

  set μ : ℝ := Real.exp (-((L : ℝ) * |(e i).re|)) with hμ
  have hμ0 : 0 < μ := Real.exp_pos _
  have hμle : ∀ t : Fin L, μ ≤ ‖((α t : ℝ) : ℂ) ^ e i‖ := by
    intro t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hα0 t)]
    show Real.exp (-((L : ℝ) * |(e i).re|)) ≤ Real.exp (-(t : ℝ)) ^ (e i).re
    rw [← Real.exp_mul, Real.exp_le_exp]
    have ht : ((t : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast t.2.le
    have h0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
    have : (t : ℝ) * (e i).re ≤ (L : ℝ) * |(e i).re| := by
      calc (t : ℝ) * (e i).re ≤ (t : ℝ) * |(e i).re| := by
              exact mul_le_mul_of_nonneg_left (le_abs_self _) h0
        _ ≤ (L : ℝ) * |(e i).re| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    linarith
  refine ⟨CV * (C'' / μ), fun k hk y₂ hy0 hy1 => ?_⟩

  set v : Fin L → ℂ := fun s =>
    if h : (j : ℕ) + (s : ℕ) < J then
      ((((j : ℕ) + (s : ℕ)).choose (j : ℕ) : ℕ) : ℂ) * c i ⟨(j : ℕ) + (s : ℕ), h⟩ y₂ k
    else 0 with hv

  have hsys : ∀ t : Fin L, ‖∑ s : Fin L, x t ^ (s : ℕ) • v s‖ ≤ C'' / μ * y₂ ^ (ρ + δ) := by
    intro t
    have hkt : a t * k ∈ K' := Set.mem_iUnion.2 ⟨t, Set.mem_image_of_mem _ hk⟩
    have hflat_t : ‖c i j y₂ (a t * k)‖ ≤ C'' * y₂ ^ (ρ + δ) :=
      le_trans (hC' _ hkt y₂ hy0 hy1)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hy0.le _))
    have hresc := coeff_rescale u e he ρ δ hδ hre c hexp i j k y₂ hy0 (α t) (hα0 t) (hα1 t)

    have hsum : (∑ j'' : Fin J, if (j : ℕ) ≤ (j'' : ℕ) then
        c i j'' y₂ k * ((α t : ℝ) : ℂ) ^ e i * ((Real.log (α t) : ℝ) : ℂ) ^ ((j'' : ℕ) - (j : ℕ)) *
          (((j'' : ℕ).choose (j : ℕ) : ℕ) : ℂ) else 0) =
        ((α t : ℝ) : ℂ) ^ e i * ∑ s : Fin L, x t ^ (s : ℕ) • v s := by
      set g : ℕ → ℂ := fun m => if h : m < J then
          c i ⟨m, h⟩ y₂ k * ((α t : ℝ) : ℂ) ^ e i * ((Real.log (α t) : ℝ) : ℂ) ^ (m - (j : ℕ)) *
            ((m.choose (j : ℕ) : ℕ) : ℂ) else 0 with hg
      have h1 : (∑ j'' : Fin J, if (j : ℕ) ≤ (j'' : ℕ) then
          c i j'' y₂ k * ((α t : ℝ) : ℂ) ^ e i * ((Real.log (α t) : ℝ) : ℂ) ^ ((j'' : ℕ) - (j : ℕ)) *
            (((j'' : ℕ).choose (j : ℕ) : ℕ) : ℂ) else 0) =
          ∑ j'' : Fin J, if (j : ℕ) ≤ (j'' : ℕ) then g j'' else 0 := by
        refine Finset.sum_congr rfl (fun j'' _ => ?_)
        simp only [hg, dif_pos j''.2]
      rw [h1, sum_ite_le_eq_sum_offset J j g, ← hL, ← Fin.sum_univ_eq_sum_range (fun s => g ((j : ℕ) + s)) L,
        Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      have hs : (j : ℕ) + (s : ℕ) < J := by have := s.2; omega
      simp only [hg, hv, dif_pos hs, hx, hlogα, smul_eq_mul, Nat.add_sub_cancel_left]
      ring
    have hid : c i j y₂ (a t * k) = ((α t : ℝ) : ℂ) ^ e i * ∑ s : Fin L, x t ^ (s : ℕ) • v s := by
      rw [← hsum]; exact hresc
    have hn : ‖((α t : ℝ) : ℂ) ^ e i‖ * ‖∑ s : Fin L, x t ^ (s : ℕ) • v s‖ ≤ C'' * y₂ ^ (ρ + δ) := by
      rw [← norm_mul, ← hid]; exact hflat_t
    have hpos : 0 < ‖((α t : ℝ) : ℂ) ^ e i‖ := lt_of_lt_of_le hμ0 (hμle t)
    rw [div_mul_eq_mul_div, le_div_iff₀ hμ0]
    calc ‖∑ s : Fin L, x t ^ (s : ℕ) • v s‖ * μ ≤ ‖∑ s : Fin L, x t ^ (s : ℕ) • v s‖ * ‖((α t : ℝ) : ℂ) ^ e i‖ :=
          mul_le_mul_of_nonneg_left (hμle t) (norm_nonneg _)
      _ = ‖((α t : ℝ) : ℂ) ^ e i‖ * ‖∑ s : Fin L, x t ^ (s : ℕ) • v s‖ := mul_comm _ _
      _ ≤ C'' * y₂ ^ (ρ + δ) := hn
  have hVm := hV ℂ v (C'' / μ * y₂ ^ (ρ + δ)) hsys ⟨(j' : ℕ) - (j : ℕ), hLpos⟩

  have hjJ : (j : ℕ) + ((j' : ℕ) - (j : ℕ)) < J := by have := j'.2; have : (j:ℕ) ≤ (j':ℕ) := hjj'; omega
  have hvj : v ⟨(j' : ℕ) - (j : ℕ), hLpos⟩ = (((j' : ℕ).choose (j : ℕ) : ℕ) : ℂ) * c i j' y₂ k := by
    simp only [hv, dif_pos hjJ]
    have : (⟨(j : ℕ) + ((j' : ℕ) - (j : ℕ)), hjJ⟩ : Fin J) = j' := by
      apply Fin.ext; show (j : ℕ) + ((j' : ℕ) - (j : ℕ)) = (j' : ℕ); have : (j:ℕ) ≤ (j':ℕ) := hjj'; omega
    rw [this]
    have : (j : ℕ) + ((j' : ℕ) - (j : ℕ)) = (j' : ℕ) := by have : (j:ℕ) ≤ (j':ℕ) := hjj'; omega
    rw [this]
  rw [hvj, norm_mul] at hVm
  have hchoose : (1 : ℝ) ≤ ‖((((j' : ℕ).choose (j : ℕ) : ℕ)) : ℂ)‖ := by
    rw [Complex.norm_natCast]
    exact_mod_cast Nat.choose_pos hjj'
  calc ‖c i j' y₂ k‖ ≤ ‖((((j' : ℕ).choose (j : ℕ) : ℕ)) : ℂ)‖ * ‖c i j' y₂ k‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hchoose
    _ ≤ CV * (C'' / μ * y₂ ^ (ρ + δ)) := hVm
    _ = CV * (C'' / μ) * y₂ ^ (ρ + δ) := by ring

end WsB.FU

open WsB.FU in
theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (N₂ : ℕ) (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1)
    (N₃ : ℕ) (a₃ : Fin (N₃ + 1) → ℂ) (ha₃ : a₃ (Fin.last N₃) = 1) :
    ∀ ρ : ℝ, ∀ (n J : ℕ) (e : Fin n → ℂ) (δ : ℝ), 0 < δ → Function.Injective e →
      (∀ i, (e i).re ≤ ρ) →
      ∀ (N : ℕ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w)) →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g) →
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g) →
      WhittakerBlock.IsArchSmooth3 u →
      (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) →
      (∑ m, a₂ m • (WhittakerBlock.casimir2^[m] u) = 0) →
      (∑ m, a₃ m • (WhittakerBlock.casimir3^[m] u) = 0) →
      (∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w g‖ ≤ C * gauge3 ℚ g ^ N) →
      ∀ (c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1}) →
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ (ρ + δ)) →
        ∀ (i : Fin n) (j : Fin J),
            (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K,
              ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 → ‖c i j y₂ k‖ ≤ C * y₂ ^ (ρ + δ)) →
            ∀ (j' : Fin J), j ≤ j' →
              (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K,
              ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 → ‖c i j' y₂ k‖ ≤ C * y₂ ^ (ρ + δ)) :=
  fun ρ n J e δ hδ he hre N u _ _ _ _ _ _ _ _ c _ hexp i j hflat j' hjj' =>
    climb u e he ρ δ hδ hre c hexp i j hflat j' hjj'

end
end S_LanglandsTunnell_CubicInduction_firstRatioCoeff_flat_of_le_of_flat_of_casimir_relations
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_firstRatioCoeff_flat_of_le_of_flat_of_casimir_relations (solution)
