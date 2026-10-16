-- Prove2me | solution 1 for OAI.GAD.output_entropy_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:04:58.434409+00:00
-- url     : https://prove2.me/submissions/35351f12-2da6-4ce1-b1ae-f9954953fcbb

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/PureRecursion.lean:L264-L309
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.output_entropy_recursion. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PureRecursion
import Theorems.Thm_OAI_GAD_channel_first_site_entry
import Theorems.Thm_OAI_GAD_entropy_reindex
import Theorems.Thm_OAI_GAD_kraus_complete
import Theorems.Thm_OAI_GAD_local_channel
import Theorems.Thm_OAI_GAD_thermal_entropy

-- ---- from OAI.InformationTheory.AmplitudeDamping.Channel ----
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem sum_fin_cons {α : Type u_1} {M : Type u_2} [Fintype α] [AddCommMonoid M] {n : ℕ}
    (f : (Fin (n+1) → α) → M) :
    ∑ r, f r = ∑ a, ∑ r : Fin n → α, f (Fin.cons a r) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) ↦ α)).sum_comp f]
  rw [Fintype.sum_prod_type]
  rfl

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem tensorKraus_complete (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) :
    ∑ r, (tensorKraus γ ν n r).conjTranspose * tensorKraus γ ν n r = 1 := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, tensorKraus,
    star_prod]
  simp only [← Finset.prod_mul_distrib]
  have hinner (r : Fin n → Fin 4) :
      (∑ b : Basis n, ∏ k, star (kraus γ ν (r k) (b k) (i k)) * kraus γ ν (r k) (b k) (j k)) =
      ∏ k, ∑ b : Fin 2, star (kraus γ ν (r k) b (i k)) * kraus γ ν (r k) b (j k) :=
    (Fintype.prod_sum (fun k b ↦ star (kraus γ ν (r k) b (i k)) * kraus γ ν (r k) b (j k))).symm
  simp only [hinner]
  rw [← Fintype.prod_sum (fun k r ↦ ∑ b : Fin 2,
    star (kraus γ ν r b (i k)) * kraus γ ν r b (j k))]
  have hc (k : Fin n) :
      (∑ r : Fin 4, ∑ b : Fin 2, star (kraus γ ν r b (i k)) * kraus γ ν r b (j k)) =
      if i k = j k then 1 else 0 := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ ↦ A (i k) (j k))
      (kraus_complete γ ν hγ hν)
    simpa only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] using h
  simp_rw [hc]
  simp [Fintype.prod_ite_zero, funext_iff, Matrix.one_apply]

theorem applyKraus_posSemidef {ι : Type u_7} {κ : Type u_8} {ρ : Type u_9} [Fintype ι] [Fintype κ] [Fintype ρ]
    [DecidableEq ι] [DecidableEq κ] (L : ρ → Matrix ι κ ℂ)
    {P : Matrix κ κ ℂ} (hP : P.PosSemidef) : (applyKraus L P).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact Finset.sum_nonneg (fun r _ ↦ Matrix.nonneg_iff_posSemidef.mpr
    (hP.mul_mul_conjTranspose_same (L r)))

theorem applyKraus_trace {ι : Type u_10} {κ : Type u_11} {ρ : Type u_12} [Fintype ι] [Fintype κ] [Fintype ρ]
    [DecidableEq κ] (L : ρ → Matrix ι κ ℂ)
    (hL : ∑ r, (L r).conjTranspose * L r = 1) (P : Matrix κ κ ℂ) :
    (applyKraus L P).trace = P.trace := by
  simp only [applyKraus, Matrix.trace_sum]
  calc
    _ = ∑ r, ((L r).conjTranspose * L r * P).trace := by
      apply Finset.sum_congr rfl
      intro r _
      exact Matrix.trace_mul_cycle _ _ _
    _ = _ := by
      rw [← Matrix.trace_sum, ← Matrix.sum_mul, hL, Matrix.one_mul]

theorem channel_trace (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) (P : QMatrix n) :
    (channel γ ν n P).trace = P.trace :=
  applyKraus_trace _ (tensorKraus_complete γ ν hγ hν n) P

theorem channel_posSemidef (γ ν : ℝ) (n : ℕ) {P : QMatrix n} (hP : P.PosSemidef) :
    (channel γ ν n P).PosSemidef := applyKraus_posSemidef _ hP

theorem columns_mul_conjTranspose {ι : Type u_18} {κ : Type u_19} {ρ : Type u_20} [Fintype κ] [Fintype ρ]
    (L : ρ → Matrix ι κ ℂ) (ψ φ : κ → ℂ) :
    columns L ψ * (columns L φ).conjTranspose =
      ∑ r, L r * Matrix.vecMulVec ψ (star φ) * (L r).conjTranspose := by
  simp_rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]
  ext i j
  simp [columns, Matrix.mul_apply, Matrix.vecMulVec, Matrix.conjTranspose_apply, Matrix.sum_apply]

theorem columns_pure {ι : Type u_21} {κ : Type u_22} {ρ : Type u_23} [Fintype κ] [Fintype ρ]
    (L : ρ → Matrix ι κ ℂ) (ψ : κ → ℂ) :
    columns L ψ * (columns L ψ).conjTranspose = applyKraus L (pure ψ) :=
  columns_mul_conjTranspose L ψ ψ

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.GramMatrices ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {κ : Type u_2} {μ : Type u_3} {ν : Type u_4} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem gram_sqrt_smul {r : ℝ} (hr : 0 ≤ r) (A : Matrix ι κ ℂ) :
    gram (Real.sqrt r • A) = r • gram A := by
  simp only [gram, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Real.mul_self_sqrt hr]

end GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_5} [Fintype ι] [DecidableEq ι]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.PureRecursion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

namespace GAD

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_1} [Fintype ι]

theorem vecMass_nonneg (ψ : ι → ℂ) : 0 ≤ vecMass ψ :=
  Finset.sum_nonneg (fun i _ ↦ Complex.normSq_nonneg (ψ i))

theorem vecMass_eq_zero {ψ : ι → ℂ} : vecMass ψ = 0 ↔ ψ = 0 := by
  constructor
  · intro h
    funext i
    apply Complex.normSq_eq_zero.mp
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ Complex.normSq_nonneg (ψ i))).mp h i
      (Finset.mem_univ i)
  · rintro rfl
    simp [vecMass]

variable [DecidableEq ι]

omit [DecidableEq ι] in
theorem vecMass_smul (z : ℂ) (ψ : ι → ℂ) :
    vecMass (z • ψ) = Complex.normSq z * vecMass ψ := by
  simp [vecMass, Complex.normSq_mul, Finset.mul_sum]

theorem sqrt_mass_normalize [Inhabited ι] (ψ : ι → ℂ) :
    (Real.sqrt (vecMass ψ) : ℂ) • normalize ψ = ψ := by
  by_cases h : vecMass ψ = 0
  · have hz := vecMass_eq_zero.mp h
    simp [normalize,hz,vecMass]
  · have hs : (Real.sqrt (vecMass ψ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (vecMass_nonneg ψ) (Ne.symm h)))
    simp [normalize,h,smul_smul,hs]

theorem normalize_mass [Inhabited ι] (ψ : ι → ℂ) : vecMass (normalize ψ) = 1 := by
  by_cases h : vecMass ψ = 0
  · simp [normalize,h]
  · have hs : Real.sqrt (vecMass ψ)*Real.sqrt (vecMass ψ) = vecMass ψ := Real.mul_self_sqrt (vecMass_nonneg ψ)
    simp only [normalize, ite_eq_right h, vecMass_smul, map_inv₀, Complex.normSq_ofReal, hs]
    exact inv_mul_cancel₀ h

end

section
open scoped BigOperators ComplexOrder
open Matrix

theorem vecMass_branches {n : ℕ} (ψ : Basis (n+1) → ℂ) :
    vecMass ψ = vecMass (branch ψ 0) + vecMass (branch ψ 1) := by
  unfold vecMass
  rw [sum_fin_cons]
  simp [Fin.sum_univ_two,branch]

theorem population_zero {n : ℕ} (ψ : Basis (n+1) → ℂ) :
    population ψ 0 = vecMass (branch ψ 1) := by
  unfold population
  rw [sum_fin_cons]
  simp [vecMass,branch]

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

theorem channel_branch_blocks (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (ψ : Basis (n+1) → ℂ) :
    Matrix.reindex (basisSplit n).symm (basisSplit n).symm (channel γ ν (n+1) (pure ψ)) =
      thermal (columns (tensorKraus γ ν n) (branch ψ 0))
        (columns (tensorKraus γ ν n) (branch ψ 1))
        (1-γ*ν) (γ*(1-ν)) (γ*ν) (1-γ*(1-ν)) (Real.sqrt (1-γ)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm,basisSplit_inl,basisSplit_inr,
      channel_first_site_entry]
  all_goals
    rw [local_channel γ ν hγ hν (fun a d ↦
      (columns (tensorKraus γ ν n) (branch ψ a) *
        (columns (tensorKraus γ ν n) (branch ψ d)).conjTranspose) i j)]
    simp [thermal,gram]

end GAD

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

variable {ι : Type u_2} {κ : Type u_3} {ρ : Type u_4} [Fintype ι] [Fintype κ] [Fintype ρ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ]

omit [Fintype ι] [Fintype ρ] [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ] in
theorem columns_smul (L : ρ → Matrix ι κ ℂ) (ψ : κ → ℂ) (z : ℂ) :
    columns L (z • ψ) = z • columns L ψ := by
  ext i r
  simp [columns, Matrix.mulVec_smul]

omit [Fintype ι] [Fintype ρ] [DecidableEq ι] [DecidableEq ρ] in
theorem columns_normalize [Inhabited κ] (L : ρ → Matrix ι κ ℂ) (ψ : κ → ℂ) :
    columns L ψ = Real.sqrt (vecMass ψ) • columns L (normalize ψ) := by
  rw [← Complex.coe_smul, ← columns_smul, sqrt_mass_normalize]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ] in
theorem gram_columns (L : ρ → Matrix ι κ ℂ) (ψ : κ → ℂ) :
    gram (columns L ψ) = applyKraus L (pure ψ) := columns_pure L ψ

theorem mass_channel_columns (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) (ψ : Basis n → ℂ) :
    mass (columns (tensorKraus γ ν n) ψ) = vecMass ψ := by
  unfold mass
  rw [gram_columns]
  change (channel γ ν n (pure ψ)).trace.re = _
  rw [channel_trace γ ν hγ hν, pure_trace,Complex.ofReal_re]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem thermal_sqrt_smul (X Y : Matrix ι κ ℂ) (a b c d K : ℝ)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    thermal (Real.sqrt x • X) (Real.sqrt y • Y) a b c d K =
      thermal X Y (a*x) (b*y) (c*x) (d*y) (K*Real.sqrt x*Real.sqrt y) := by
  simp only [thermal,gram_sqrt_smul hx,gram_sqrt_smul hy,smul_smul,
    Matrix.conjTranspose_smul, star_trivial,Matrix.smul_mul,Matrix.mul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

theorem output_entropy_recursion (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (ψ : Basis (n+1) → ℂ)
    (hψ : vecMass ψ = 1) :
    vecMass (branch ψ 0) * entropy (channel γ ν n (pure (normalize (branch ψ 0)))) +
      vecMass (branch ψ 1) * entropy (channel γ ν n (pure (normalize (branch ψ 1)))) +
      g (v γ ν (population ψ 0)) ≤ entropy (channel γ ν (n+1) (pure ψ)) := by
  let x := vecMass (branch ψ 0)
  let y := vecMass (branch ψ 1)
  let X := columns (tensorKraus γ ν n) (normalize (branch ψ 0))
  let Y := columns (tensorKraus γ ν n) (normalize (branch ψ 1))
  have hx : 0 ≤ x := vecMass_nonneg _
  have hy : 0 ≤ y := vecMass_nonneg _
  have hxy : x+y=1 := (vecMass_branches ψ).symm.trans hψ
  have hxy' : x=1-y := by linarith
  have hX : mass X = 1 := (mass_channel_columns γ ν hγ hν n _).trans (normalize_mass _)
  have hY : mass Y = 1 := (mass_channel_columns γ ν hγ hν n _).trans (normalize_mass _)
  have h1ν : 0 ≤ 1-ν := sub_nonneg.mpr hν.2
  have h1γ : 0 ≤ 1-γ := sub_nonneg.mpr hγ.2
  have h1γν : 0 ≤ 1-γ*ν := by nlinarith [hγ.2, mul_nonneg hγ.1 h1ν]
  have h1γν' : 0 ≤ 1-γ*(1-ν) := by nlinarith [hγ.2, mul_nonneg hγ.1 hν.1]
  have hKsq : (Real.sqrt (1-γ)*Real.sqrt x*Real.sqrt y)^2 = (1-γ)*x*y := by
    rw [mul_pow,mul_pow,Real.sq_sqrt h1γ,Real.sq_sqrt hx,Real.sq_sqrt hy]
  have hh := thermal_entropy X Y hX hY
    (mul_nonneg h1γν hx) (mul_nonneg (mul_nonneg hγ.1 h1ν) hy)
    (mul_nonneg (mul_nonneg hγ.1 hν.1) hx) (mul_nonneg h1γν' hy)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    (show (1-γ*ν)*x+γ*(1-ν)*y+γ*ν*x+(1-γ*(1-ν))*y=1 by nlinarith only [hxy])
    (show ((1-γ*ν)*x)*((1-γ*(1-ν))*y)-(γ*(1-ν)*y)*(γ*ν*x)=
      (Real.sqrt (1-γ)*Real.sqrt x*Real.sqrt y)^2 by rw [hKsq]; ring)
  have hcolx : (1-γ*ν)*x+γ*ν*x=x := by ring
  have hcoly : γ*(1-ν)*y+(1-γ*(1-ν))*y=y := by ring
  have hu : ((1-γ*ν)*x+γ*(1-ν)*y)*(γ*ν*x+(1-γ*(1-ν))*y)-
      (Real.sqrt (1-γ)*Real.sqrt x*Real.sqrt y)^2 = v γ ν y := by
    rw [hKsq,hxy']; unfold v; ring
  have heq : Matrix.reindex (basisSplit n).symm (basisSplit n).symm
      (channel γ ν (n+1) (pure ψ)) =
        thermal X Y ((1-γ*ν)*x) (γ*(1-ν)*y) (γ*ν*x) ((1-γ*(1-ν))*y)
          (Real.sqrt (1-γ)*Real.sqrt x*Real.sqrt y) := by
    rw [channel_branch_blocks γ ν hγ hν,columns_normalize _ (branch ψ 0),
      columns_normalize _ (branch ψ 1),thermal_sqrt_smul _ _ _ _ _ _ _ hx hy]
  have hent := entropy_reindex (basisSplit n).symm
    (channel_posSemidef γ ν (n+1) (pure_posSemidef ψ)).isHermitian
  rw [heq] at hent
  have hbound := hh.2.2
  rw [hcolx,hcoly,hu,hent] at hbound
  simpa only [x,y,X,Y,gram_columns,population_zero,channel,applyKraus] using hbound

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.output_entropy_recursion := @_root_.OAI.GAD.output_entropy_recursion
