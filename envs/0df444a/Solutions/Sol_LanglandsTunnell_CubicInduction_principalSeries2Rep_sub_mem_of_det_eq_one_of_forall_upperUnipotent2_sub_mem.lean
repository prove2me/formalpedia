-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.principalSeries2Rep_sub_mem_of_det_eq_one_of_forall_upperUnipotent2_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/bd0cf296-affa-5285-9085-950b91d644b8

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_principalSeries2Rep_sub_mem_of_det_eq_one_of_forall_upperUnipotent2_sub_mem

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

noncomputable section

namespace WsF
namespace W5a

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => p.adicCompletion ℚ
local notation "G" => GL (Fin 2) (p.adicCompletion ℚ)

def lowerUnipotent2 (c : F) : G where
  val := !![1, 0; c, 1]
  inv := !![1, 0; -c, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem lowerUnipotent2_coe (c : F) :
    (lowerUnipotent2 c : Matrix (Fin 2) (Fin 2) F) = !![1, 0; c, 1] := rfl

def w0 : G where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem w0_inv : (w0 : G)⁻¹ = w0 := Units.ext rfl

theorem lowerUnipotent2_eq_conj (c : F) : lowerUnipotent2 c = w0 * upperUnipotent2 p c * w0⁻¹ := by
  rw [w0_inv]
  apply Units.ext
  simp only [Units.val_mul, lowerUnipotent2_coe, upperUnipotent2_coe, w0]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem eq_unipotent_prod_of_corner_ne_zero (g : G)
    (hdet : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 1)
    (hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    g = upperUnipotent2 p (((g : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) / (g : Matrix (Fin 2) (Fin 2) F) 1 0) *
      lowerUnipotent2 ((g : Matrix (Fin 2) (Fin 2) F) 1 0) *
      upperUnipotent2 p (((g : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) / (g : Matrix (Fin 2) (Fin 2) F) 1 0) := by
  apply Units.ext
  simp only [Units.val_mul, lowerUnipotent2_coe, upperUnipotent2_coe]
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
  all_goals first | ring1 | linear_combination hdet | linear_combination (-1 : F) * hdet

variable (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))

def trivSubgroup (V : Submodule ℂ ↥(principalSeries2 p θ))
    (hV : ∀ (g : G), ∀ v ∈ V, principalSeries2Rep θ g v ∈ V) : Subgroup G where
  carrier := {g | ∀ f : ↥(principalSeries2 p θ), principalSeries2Rep θ g f - f ∈ V}
  one_mem' := fun f => by simp
  mul_mem' := by
    intro g h hg hh f
    have e : principalSeries2Rep θ (g * h) f - f =
        principalSeries2Rep θ g (principalSeries2Rep θ h f - f) + (principalSeries2Rep θ g f - f) := by
      rw [map_mul, Module.End.mul_apply, map_sub]; abel
    rw [e]
    exact V.add_mem (hV g _ (hh f)) (hg f)
  inv_mem' := by
    intro g hg f
    have e : principalSeries2Rep θ g⁻¹ f - f = -(principalSeries2Rep θ g⁻¹ (principalSeries2Rep θ g f - f)) := by
      rw [map_sub, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]; abel
    rw [e]
    exact V.neg_mem (hV _ _ (hg f))

theorem mem_trivSubgroup {V : Submodule ℂ ↥(principalSeries2 p θ)}
    {hV : ∀ (g : G), ∀ v ∈ V, principalSeries2Rep θ g v ∈ V} {g : G} :
    g ∈ trivSubgroup θ V hV ↔ ∀ f : ↥(principalSeries2 p θ), principalSeries2Rep θ g f - f ∈ V := Iff.rfl

theorem conj_mem_trivSubgroup {V : Submodule ℂ ↥(principalSeries2 p θ)}
    {hV : ∀ (g : G), ∀ v ∈ V, principalSeries2Rep θ g v ∈ V} {n : G} (hn : n ∈ trivSubgroup θ V hV) (h : G) :
    h * n * h⁻¹ ∈ trivSubgroup θ V hV := by
  intro f
  have e : principalSeries2Rep θ (h * n * h⁻¹) f - f =
      principalSeries2Rep θ h (principalSeries2Rep θ n (principalSeries2Rep θ h⁻¹ f) - principalSeries2Rep θ h⁻¹ f) := by
    rw [map_sub, ← Module.End.mul_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [e]
  exact hV _ _ (hn _)

theorem sub_mem_of_det_eq_one (V : Submodule ℂ ↥(principalSeries2 p θ))
    (hV : ∀ (g : G), ∀ v ∈ V, principalSeries2Rep θ g v ∈ V)
    (hq : ∀ (x : F) (f : ↥(principalSeries2 p θ)), principalSeries2Rep θ (upperUnipotent2 p x) f - f ∈ V)
    (g : G) (hg : Matrix.GeneralLinearGroup.det g = 1) (f : ↥(principalSeries2 p θ)) :
    principalSeries2Rep θ g f - f ∈ V := by
  let S := trivSubgroup θ V hV
  have hN : ∀ x : F, upperUnipotent2 p x ∈ S := fun x f => hq x f
  have hNm : ∀ c : F, lowerUnipotent2 c ∈ S := fun c => by
    rw [lowerUnipotent2_eq_conj]; exact conj_mem_trivSubgroup θ (hN c) w0
  have hdet : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) hg
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_fin_two] at this
    exact this

  have big : ∀ g' : G, (g' : Matrix (Fin 2) (Fin 2) F) 0 0 * (g' : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (g' : Matrix (Fin 2) (Fin 2) F) 0 1 * (g' : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 →
      (g' : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 → g' ∈ S := by
    intro g' hd hc
    rw [eq_unipotent_prod_of_corner_ne_zero g' hd hc]
    exact S.mul_mem (S.mul_mem (hN _) (hNm _)) (hN _)
  suffices hS : g ∈ S from hS f
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  ·
    have hg' : g = g * lowerUnipotent2 (1 : F) * (lowerUnipotent2 (1 : F))⁻¹ := by group
    have hd11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
      intro h11; rw [hc, h11] at hdet; simp at hdet
    rw [hg']
    refine S.mul_mem (big _ ?_ ?_) (S.inv_mem (hNm 1))
    · simp only [Units.val_mul, lowerUnipotent2_coe, Matrix.mul_apply, Fin.sum_univ_two]
      simp
      linear_combination hdet
    · simp only [Units.val_mul, lowerUnipotent2_coe, Matrix.mul_apply, Fin.sum_univ_two]
      simpa [hc] using hd11
  · exact big g hdet hc

end WsF.W5a
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_principalSeries2Rep_sub_mem_of_det_eq_one_of_forall_upperUnipotent2_sub_mem.WsF P2MW.S_LanglandsTunnell_CubicInduction_principalSeries2Rep_sub_mem_of_det_eq_one_of_forall_upperUnipotent2_sub_mem.WsF.W5a"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_principalSeries2Rep_sub_mem_of_det_eq_one_of_forall_upperUnipotent2_sub_mem.WsF"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_principalSeries2Rep_sub_mem_of_det_eq_one_of_forall_upperUnipotent2_sub_mem.WsF P2MW.S_LanglandsTunnell_CubicInduction_principalSeries2Rep_sub_mem_of_det_eq_one_of_forall_upperUnipotent2_sub_mem.WsF.W5a"

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (V : Submodule ℂ ↥(principalSeries2 p θ))
    (hV : ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)), ∀ v ∈ V, principalSeries2Rep θ g v ∈ V)
    (hq : ∀ (x : p.adicCompletion ℚ) (f : ↥(principalSeries2 p θ)), principalSeries2Rep θ (upperUnipotent2 p x) f - f ∈ V)
    (g : GL (Fin 2) (p.adicCompletion ℚ)) (hg : Matrix.GeneralLinearGroup.det g = 1)
    (f : ↥(principalSeries2 p θ)) :
    principalSeries2Rep θ g f - f ∈ V :=
  WsF.W5a.sub_mem_of_det_eq_one θ V hV hq g hg f

end S_LanglandsTunnell_CubicInduction_principalSeries2Rep_sub_mem_of_det_eq_one_of_forall_upperUnipotent2_sub_mem
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_principalSeries2Rep_sub_mem_of_det_eq_one_of_forall_upperUnipotent2_sub_mem (solution)
