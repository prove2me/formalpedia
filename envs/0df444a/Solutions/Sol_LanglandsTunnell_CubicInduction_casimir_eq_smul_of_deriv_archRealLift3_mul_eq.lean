-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.casimir_eq_smul_of_deriv_archRealLift3_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d9c92bcd-156c-53d7-8a34-9107e99bd3ca

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Theorems.Thm_LanglandsTunnell_CubicInduction_casimir_apply_eq_sum_deriv_archRealLift3_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_isArchSmooth3_deriv_archRealLift3_mul_and_linear_and_bracket
import Theorems.Thm_LanglandsTunnell_CubicInduction_archRealLift3_mul_eq_mul_archRealLift3_conj
import Theorems.Thm_LanglandsTunnell_CubicInduction_gl3_casimir_normalForm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_casimir_eq_smul_of_deriv_archRealLift3_mul_eq

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_casimir_eq_smul_of_deriv_archRealLift3_mul_eq.LanglandsTunnell.CubicInduction"
open LanglandsTunnell.CubicInduction.WhittakerBlock

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.casimir_apply_eq_sum_deriv_archRealLift3_mul CubicInduction.gl3_casimir_normalForm"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.casimir1 WhittakerBlock.casimir2 WhittakerBlock.casimir3 AdelicGL archComponent3 casimir_apply_eq_sum_deriv_archRealLift3_mul isArchSmooth3_deriv_archRealLift3_mul_and_linear_and_bracket archRealLift3_mul_eq_mul_archRealLift3_conj gl3_casimir_normalForm"
namespace InfCharAsm
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

def dirEntries (X : Fin 3 → Fin 3 → ℝ) (s : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => (if a = b then (1 : ℝ) else 0) + s * X a b

def ind (i j : Fin 3) : Fin 3 → Fin 3 → ℝ := fun a b => if a = i ∧ b = j then 1 else 0

theorem unipotent_eq_dirEntries (i j : Fin 3) (s : ℝ) :
    (fun a b : Fin 3 => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) = dirEntries (ind i j) s := by
  funext a b
  simp only [dirEntries, ind, mul_ite, mul_one, mul_zero]

def L (X : Fin 3 → Fin 3 → ℝ) (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  deriv (fun s : ℝ => ψ (WhittakerBlock.archRealLift3 (dirEntries X s) * g)) 0

theorem L_def (X : Fin 3 → Fin 3 → ℝ) (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    L X ψ g = deriv (fun s : ℝ => ψ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * X a b) * g)) 0 := rfl

theorem isOpen_invertible : IsOpen {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
  isOpen_ne.preimage (Continuous.matrix_det (continuous_matrix fun a b =>
    (continuous_apply b).comp (continuous_apply a)))

theorem det_dirEntries_eventually (X : Fin 3 → Fin 3 → ℝ) :
    ∀ᶠ s in nhds (0 : ℝ), (Matrix.of (dirEntries X s)).det ≠ 0 := by
  have hc : Continuous fun s : ℝ => (Matrix.of (dirEntries X s)).det :=
    Continuous.matrix_det (continuous_matrix fun a b => by
      simp only [Matrix.of_apply, dirEntries]; fun_prop)
  have h0 : (Matrix.of (dirEntries X 0)).det ≠ 0 := by
    have : Matrix.of (dirEntries X 0) = 1 := by
      ext a b; simp [dirEntries, Matrix.one_apply]
    rw [this, Matrix.det_one]; exact one_ne_zero
  exact hc.continuousAt.eventually_ne h0

theorem differentiableAt_L {ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hψ : WhittakerBlock.IsArchSmooth3 ψ) (X : Fin 3 → Fin 3 → ℝ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    DifferentiableAt ℝ (fun s : ℝ => ψ (WhittakerBlock.archRealLift3 (dirEntries X s) * g)) 0 := by
  obtain ⟨hcdet, -⟩ := archRealLift3_mul_eq_mul_archRealLift3_conj g (dirEntries X 0) (by
    have : Matrix.of (dirEntries X 0) = 1 := by ext a b; simp [dirEntries, Matrix.one_apply]
    rw [this, Matrix.det_one]; exact one_ne_zero)
  set c : Matrix (Fin 3) (Fin 3) ℝ := StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g) with hc

  set γ : ℝ → (Fin 3 → Fin 3 → ℝ) := fun s a b => (c⁻¹ * Matrix.of (dirEntries X s) * c) a b with hγ
  have hev : (fun s : ℝ => ψ (WhittakerBlock.archRealLift3 (dirEntries X s) * g)) =ᶠ[nhds 0] fun s => ψ (g * WhittakerBlock.archRealLift3 (γ s)) := by
    filter_upwards [det_dirEntries_eventually X] with s hs
    rw [(archRealLift3_mul_eq_mul_archRealLift3_conj g (dirEntries X s) hs).2]
  refine (Filter.EventuallyEq.differentiableAt_iff hev).2 ?_

  have hγ0 : (Matrix.of (γ 0)).det ≠ 0 := by
    have h1 : Matrix.of (dirEntries X 0) = 1 := by ext a b; simp [dirEntries, Matrix.one_apply]
    have : Matrix.of (γ 0) = 1 := by
      ext a b
      simp only [hγ, Matrix.of_apply, h1, Matrix.mul_one, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hcdet)]
    rw [this, Matrix.det_one]; exact one_ne_zero
  have hd : DifferentiableAt ℝ (fun e : Fin 3 → Fin 3 → ℝ => ψ (g * WhittakerBlock.archRealLift3 e)) (γ 0) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_invertible).1 (hψ g)).1.differentiableAt
      (isOpen_invertible.mem_nhds hγ0)
  have hγd : DifferentiableAt ℝ γ 0 := by
    rw [hγ]
    refine differentiableAt_pi.2 fun a => differentiableAt_pi.2 fun b => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply, dirEntries]
    fun_prop
  exact hd.comp 0 hγd

def Lop (X : Fin 3 → Fin 3 → ℝ) : smoothFunctions3 →ₗ[ℂ] smoothFunctions3 where
  toFun ψ := ⟨fun g => L X ψ g, (isArchSmooth3_deriv_archRealLift3_mul_and_linear_and_bracket _ ψ.2).1 X⟩
  map_add' ψ₁ ψ₂ := Subtype.ext <| funext fun g =>
    ((differentiableAt_L ψ₁.2 X g).hasDerivAt.add (differentiableAt_L ψ₂.2 X g).hasDerivAt).deriv
  map_smul' c ψ := Subtype.ext <| funext fun g =>
    ((differentiableAt_L ψ.2 X g).hasDerivAt.const_smul c).deriv

@[scoped simp] theorem coe_Lop_apply (X : Fin 3 → Fin 3 → ℝ) (ψ : smoothFunctions3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((Lop X ψ : smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g = L X ψ g := rfl

theorem Lop_mul_apply (X Y : Fin 3 → Fin 3 → ℝ) (ψ : smoothFunctions3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (((Lop Y * Lop X) ψ : smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g =
      deriv (fun t : ℝ => deriv (fun s : ℝ => (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * X a b) *
          (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + t * Y a b) * g))) 0) 0 := rfl

theorem Lop_bracket (X Y : Fin 3 → Fin 3 → ℝ) :
    Lop Y * Lop X - Lop X * Lop Y = Lop (fun a b => (Matrix.of X * Matrix.of Y - Matrix.of Y * Matrix.of X) a b) := by
  apply LinearMap.ext; intro ψ; apply Subtype.ext; funext g
  rw [LinearMap.sub_apply, Submodule.coe_sub, Pi.sub_apply, Lop_mul_apply, Lop_mul_apply, coe_Lop_apply, L_def]
  exact (isArchSmooth3_deriv_archRealLift3_mul_and_linear_and_bracket _ ψ.2).2.2 X Y g

theorem Lop_lin (X Y : Fin 3 → Fin 3 → ℝ) (α β : ℝ) :
    Lop (fun a b => α * X a b + β * Y a b) = (α : ℂ) • Lop X + (β : ℂ) • Lop Y := by
  apply LinearMap.ext; intro ψ; apply Subtype.ext; funext g
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
    Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    coe_Lop_apply, coe_Lop_apply, coe_Lop_apply, L_def, L_def, L_def]
  exact (isArchSmooth3_deriv_archRealLift3_mul_and_linear_and_bracket _ ψ.2).2.1 X Y α β g

def e (i j : Fin 3) : Module.End ℂ smoothFunctions3 := Lop (ind j i)

theorem ind_mul_ind (i j k l : Fin 3) :
    Matrix.of (ind i j) * Matrix.of (ind k l) = if j = k then Matrix.of (ind i l) else 0 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single j (fun c _ hc => by simp [ind, hc]) (fun h => absurd (Finset.mem_univ j) h)]
  by_cases hjk : j = k <;> by_cases hai : a = i <;> by_cases hbl : b = l <;>
    simp [ind, hjk, hai, hbl]

theorem e_comm (i j k l : Fin 3) :
    e i j * e k l - e k l * e i j = (if j = k then e i l else (0 : Module.End ℂ smoothFunctions3)) -
      (if l = i then e k j else (0 : Module.End ℂ smoothFunctions3)) := by
  unfold e
  rw [Lop_bracket]

  rw [ind_mul_ind, ind_mul_ind]
  have key : (fun a b => ((if k = j then Matrix.of (ind l i) else 0) - (if i = l then Matrix.of (ind j k) else 0) :
      Matrix (Fin 3) (Fin 3) ℝ) a b) = fun a b => (if j = k then (1 : ℝ) else 0) * ind l i a b + (if l = i then (-1 : ℝ) else 0) * ind j k a b := by
    funext a b
    by_cases hjk : j = k <;> by_cases hli : l = i
    · subst hjk; subst hli; simp [Matrix.sub_apply]; ring
    · subst hjk; have hil : ¬ i = l := fun h => hli h.symm; simp [Matrix.sub_apply, hil, hli]
    · subst hli; have hkj : ¬ k = j := fun h => hjk h.symm; simp [Matrix.sub_apply, hkj, hjk]
    · have hil : ¬ i = l := fun h => hli h.symm; have hkj : ¬ k = j := fun h => hjk h.symm
      simp [Matrix.sub_apply, hkj, hil, hjk, hli]
  rw [key, Lop_lin]
  by_cases hjk : j = k <;> by_cases hli : l = i
  · subst hjk; subst hli
    simp only [if_true, Complex.ofReal_one, Complex.ofReal_neg, one_smul]
    ext1 ψ; simp [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, sub_eq_add_neg]
  · subst hjk
    simp only [if_true, if_neg hli, Complex.ofReal_one, Complex.ofReal_zero, one_smul, zero_smul, add_zero]
    ext1 ψ; simp [LinearMap.sub_apply]
  · subst hli
    simp only [if_true, if_neg hjk, Complex.ofReal_one, Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, zero_add]
    ext1 ψ; simp [LinearMap.sub_apply, LinearMap.smul_apply]
  · simp only [if_neg hjk, if_neg hli, Complex.ofReal_zero, zero_smul, add_zero]
    ext1 ψ; simp [LinearMap.sub_apply]

theorem Lop_mul3_apply (X Y Z : Fin 3 → Fin 3 → ℝ) (ψ : smoothFunctions3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (((Lop Z * (Lop Y * Lop X)) ψ : smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g =
      deriv (fun u : ℝ => deriv (fun t : ℝ => deriv (fun s : ℝ => (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (WhittakerBlock.archRealLift3 (dirEntries X s) *
          (WhittakerBlock.archRealLift3 (dirEntries Y t) * (WhittakerBlock.archRealLift3 (dirEntries Z u) * g)))) 0) 0) 0 := rfl

theorem Lop_mul2_apply (X Y : Fin 3 → Fin 3 → ℝ) (ψ : smoothFunctions3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (((Lop Y * Lop X) ψ : smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g =
      deriv (fun t : ℝ => deriv (fun s : ℝ => (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (WhittakerBlock.archRealLift3 (dirEntries X s) * (WhittakerBlock.archRealLift3 (dirEntries Y t) * g))) 0) 0 := rfl

end LanglandsTunnell.CubicInduction.InfCharAsm
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_casimir_eq_smul_of_deriv_archRealLift3_mul_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_casimir_eq_smul_of_deriv_archRealLift3_mul_eq.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_casimir_eq_smul_of_deriv_archRealLift3_mul_eq.LanglandsTunnell.CubicInduction.InfCharAsm"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_casimir_eq_smul_of_deriv_archRealLift3_mul_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_casimir_eq_smul_of_deriv_archRealLift3_mul_eq.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_casimir_eq_smul_of_deriv_archRealLift3_mul_eq.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_casimir_eq_smul_of_deriv_archRealLift3_mul_eq.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_casimir_eq_smul_of_deriv_archRealLift3_mul_eq.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_casimir_eq_smul_of_deriv_archRealLift3_mul_eq.LanglandsTunnell.CubicInduction.InfCharAsm"

open LanglandsTunnell.CubicInduction.InfCharAsm in
theorem solution
    (H : Fin 3 → ℂ) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (hN : ∀ i j : Fin 3, i < j → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) * g)) 0 = 0)
    (hH : ∀ (c : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = c ∧ b = c then s else 0) * g)) 0 = H c * φ g) :
    WhittakerBlock.casimir1 φ = (H 0 + H 1 + H 2) • φ ∧
    WhittakerBlock.casimir2 φ = (H 0 ^ 2 + H 1 ^ 2 + H 2 ^ 2 - 2 * H 0 + 2 * H 2) • φ ∧
    WhittakerBlock.casimir3 φ =
      (H 0 ^ 3 + H 1 ^ 3 + H 2 ^ 3 - 2 * H 0 ^ 2 + H 1 ^ 2 + 4 * H 2 ^ 2
        - (H 0 * H 1 + H 0 * H 2 + H 1 * H 2) - 2 * H 0 - 2 * H 1 + 4 * H 2) • φ := by
  set Φ : smoothFunctions3 := ⟨φ, hsa⟩ with hΦ

  have he_diag : ∀ a : Fin 3, e a a Φ = (H a) • Φ := by
    intro a; apply Subtype.ext; funext g
    rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    show L (ind a a) φ g = H a * φ g
    have := hH a g
    simp only [unipotent_eq_dirEntries] at this
    exact this
  have he_kill : ∀ a b : Fin 3, a < b → e b a Φ = 0 := by
    intro a b hab; apply Subtype.ext; funext g
    rw [Submodule.coe_zero, Pi.zero_apply]
    show L (ind a b) φ g = 0
    have := hN a b hab g
    simp only [unipotent_eq_dirEntries] at this
    exact this
  have h10 : e 1 0 Φ = 0 := he_kill 0 1 (by decide)
  have h20 : e 2 0 Φ = 0 := he_kill 0 2 (by decide)
  have h21 : e 2 1 Φ = 0 := he_kill 1 2 (by decide)

  obtain ⟨nf2, nf3⟩ := LanglandsTunnell.CubicInduction.gl3_casimir_normalForm (A := Module.End ℂ smoothFunctions3) e e_comm

  have rw := fun g => LanglandsTunnell.CubicInduction.casimir_apply_eq_sum_deriv_archRealLift3_mul φ hsa g
  refine ⟨?_, ?_, ?_⟩
  · funext g
    rw [(rw g).1, Pi.smul_apply, smul_eq_mul]
    simp only [hH, Fin.sum_univ_three]
    ring
  · funext g
    rw [(rw g).2.1, Pi.smul_apply, smul_eq_mul]

    have hterm : ∀ i j : Fin 3,
        deriv (fun t : ℝ => deriv (fun s : ℝ =>
          φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) *
            (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = j ∧ b = i then t else 0) * g))) 0) 0
        = (((e i j * e j i) Φ : smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g := by
      intro i j
      simp only [unipotent_eq_dirEntries]
      rfl
    simp only [hterm]
    have hsum : (∑ i : Fin 3, ∑ j : Fin 3, (((e i j * e j i) Φ : smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g)
        = (((∑ i : Fin 3, ∑ j : Fin 3, e i j * e j i) Φ : smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g := by
      simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    rw [hsum, nf2]
    have hΦc : ((Φ : smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = φ := rfl
    simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, he_diag, h10, h20, h21,
      map_smul, map_zero, smul_zero, add_zero, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
      Submodule.coe_smul_of_tower, Submodule.coe_zero, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul, nsmul_eq_mul, Module.End.natCast_apply, Module.End.ofNat_apply, hΦc, Pi.mul_apply,
      Pi.ofNat_apply, Pi.natCast_apply]
    push_cast
    ring
  · funext g
    rw [(rw g).2.2, Pi.smul_apply, smul_eq_mul]
    have hterm : ∀ i j k : Fin 3,
        deriv (fun u : ℝ => deriv (fun t : ℝ => deriv (fun s : ℝ =>
          φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) *
            (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = j ∧ b = k then t else 0) *
              (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = k ∧ b = i then u else 0) * g)))) 0) 0) 0
        = (((e i k * (e k j * e j i)) Φ : smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g := by
      intro i j k
      simp only [unipotent_eq_dirEntries]
      rfl
    simp only [hterm]

    have hsum : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (((e i k * (e k j * e j i)) Φ : smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g)
        = (((∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, e i j * (e j k * e k i)) Φ : smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) g := by
      simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
    rw [hsum, nf3]
    have hΦc : ((Φ : smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = φ := rfl
    simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, he_diag, h10, h20, h21,
      map_smul, map_zero, smul_zero, add_zero, zero_add, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
      Submodule.coe_smul_of_tower, Submodule.coe_zero, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul, nsmul_eq_mul, Module.End.natCast_apply, Module.End.ofNat_apply, hΦc, Pi.mul_apply,
      Pi.ofNat_apply, Pi.natCast_apply]
    push_cast
    ring

end S_LanglandsTunnell_CubicInduction_casimir_eq_smul_of_deriv_archRealLift3_mul_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_casimir_eq_smul_of_deriv_archRealLift3_mul_eq (solution)
