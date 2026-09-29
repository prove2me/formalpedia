-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.hasWhittakerMultOne_of_isCosetEigenfunction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/299cb334-eb6b-53f9-a738-d4297b56b4fe

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Theorems.Thm_LanglandsTunnell_CubicInduction_sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_valued_eq_exp_of_coe_eq_diagonal_of_not_valued_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_hasWhittakerMultOne_of_isCosetEigenfunction

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField NumberField.AdelicLevel
open LanglandsTunnell.TateLocal
open LanglandsTunnell.CubicInduction

noncomputable section

namespace SphericalWhittakerRigidity

section SpanInheritance

variable {F : Type*} [CommRing F] {R : Type*} [CommRing R]

private theorem isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace (ψ : AddChar F R) {W : GL (Fin 3) F → R}
    (hW : IsGL3PsiWhittakerFn ψ W) {f : GL (Fin 3) F → R} (hf : f ∈ gl3CyclicSubspace W) :
    IsGL3PsiWhittakerFn ψ f := by
  have hle : gl3CyclicSubspace W ≤ gl3PsiWhittakerFnSpace F R ψ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    exact rightTranslate_mem_gl3PsiWhittakerFnSpace ψ h ((mem_gl3PsiWhittakerFnSpace_iff ψ W).mpr hW)
  exact (mem_gl3PsiWhittakerFnSpace_iff ψ f).mp (hle hf)

end SpanInheritance

section Transport

variable {F : Type*} [CommRing F]

private theorem self_mem_gl3CyclicSubspace (W : GL (Fin 3) F → ℂ) : W ∈ gl3CyclicSubspace W :=
  Submodule.subset_span ⟨1, by ext h; simp⟩

private def cyclicGenerator (W : GL (Fin 3) F → ℂ) : gl3CyclicSubspace W :=
  ⟨W, self_mem_gl3CyclicSubspace W⟩

private def whittakerFnOfFunctional (W : GL (Fin 3) F → ℂ) (L : gl3CyclicSubspace W →ₗ[ℂ] ℂ) :
    GL (Fin 3) F → ℂ :=
  fun g => L (gl3CyclicRep W g (cyclicGenerator W))

private theorem whittakerFnOfFunctional_one (W : GL (Fin 3) F → ℂ) (L : gl3CyclicSubspace W →ₗ[ℂ] ℂ) :
    whittakerFnOfFunctional W L 1 = L (cyclicGenerator W) := by
  simp [whittakerFnOfFunctional]

private theorem isGL3PsiWhittakerFn_whittakerFnOfFunctional (ψ : AddChar F ℂ) (W : GL (Fin 3) F → ℂ)
    (L : gl3CyclicSubspace W →ₗ[ℂ] ℂ) (hL : IsGL3WhittakerFunctional (gl3CyclicRep W) ψ L) :
    IsGL3PsiWhittakerFn ψ (whittakerFnOfFunctional W L) := by
  intro x y z g
  simp only [whittakerFnOfFunctional]
  rw [map_mul, Module.End.mul_apply]
  exact hL x y z _

private theorem isRightInvariant_whittakerFnOfFunctional (U : Subgroup (GL (Fin 3) F)) (W : GL (Fin 3) F → ℂ)
    (hW : IsRightInvariant U W) (L : gl3CyclicSubspace W →ₗ[ℂ] ℂ) :
    IsRightInvariant U (whittakerFnOfFunctional W L) := by
  intro g u hu
  simp only [whittakerFnOfFunctional]
  refine congrArg L (Subtype.ext (funext fun h => ?_))
  show W (h * (g * u)) = W (h * g)
  rw [← mul_assoc]
  exact hW (h * g) u hu

private theorem isCosetEigenfunction_whittakerFnOfFunctional (U : Subgroup (GL (Fin 3) F)) (gen : GL (Fin 3) F)
    (W : GL (Fin 3) F → ℂ) (lam : ℂ) (hW : IsCosetEigenfunction U gen W lam)
    (L : gl3CyclicSubspace W →ₗ[ℂ] ℂ) :
    IsCosetEigenfunction U gen (whittakerFnOfFunctional W L) lam := by
  intro ι _ reps hsys g
  have key : (∑ i, gl3CyclicRep W (g * reps i) (cyclicGenerator W)) =
      lam • gl3CyclicRep W g (cyclicGenerator W) := by
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_smul]
    funext h
    rw [Finset.sum_apply]
    show ∑ i, W (h * (g * reps i)) = lam * W (h * g)
    have hg := hW ι reps hsys (h * g)
    simp only [cosetSum, mul_assoc] at hg
    exact hg
  have hL := congrArg L key
  rw [map_sum, map_smul, smul_eq_mul] at hL
  simp only [cosetSum, whittakerFnOfFunctional]
  exact hL

private theorem whittakerFnOfFunctional_central_mul (W : GL (Fin 3) F → ℂ) (z : GL (Fin 3) F)
    (hz : ∀ h : GL (Fin 3) F, z * h = h * z) (e : ℂ) (hW : ∀ g, W (z * g) = e * W g)
    (L : gl3CyclicSubspace W →ₗ[ℂ] ℂ) (g : GL (Fin 3) F) :
    whittakerFnOfFunctional W L (z * g) = e * whittakerFnOfFunctional W L g := by
  have key : gl3CyclicRep W (z * g) (cyclicGenerator W) = e • gl3CyclicRep W g (cyclicGenerator W) := by
    apply Subtype.ext
    rw [Submodule.coe_smul]
    funext h
    show W (h * (z * g)) = e * W (h * g)
    rw [← mul_assoc, ← hz h, mul_assoc]
    exact hW (h * g)
  have hL := congrArg L key
  rw [map_smul, smul_eq_mul] at hL
  simp only [whittakerFnOfFunctional]
  exact hL

private def evalOneOnCyclic (W : GL (Fin 3) F → ℂ) : gl3CyclicSubspace W →ₗ[ℂ] ℂ :=
  (LinearMap.proj (1 : GL (Fin 3) F)).comp (gl3CyclicSubspace W).subtype

private theorem isGL3WhittakerFunctional_evalOneOnCyclic (ψ : AddChar F ℂ) (W : GL (Fin 3) F → ℂ)
    (hW : IsGL3PsiWhittakerFn ψ W) :
    IsGL3WhittakerFunctional (gl3CyclicRep W) ψ (evalOneOnCyclic W) := by
  intro x y z f
  have hf : IsGL3PsiWhittakerFn ψ (f : GL (Fin 3) F → ℂ) :=
    isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace ψ hW f.2
  show (f : GL (Fin 3) F → ℂ) (1 * upperUnipotent3 x y z) = ψ (x + y) * (f : GL (Fin 3) F → ℂ) 1
  simpa using hf x y z 1

private theorem eq_zero_of_whittakerFnOfFunctional_eq_zero (W : GL (Fin 3) F → ℂ)
    (M : gl3CyclicSubspace W →ₗ[ℂ] ℂ) (hM : whittakerFnOfFunctional W M = 0) : M = 0 := by
  have hgen : ∀ g : GL (Fin 3) F, M (gl3CyclicRep W g (cyclicGenerator W)) = 0 := fun g => congrFun hM g
  apply LinearMap.ext
  rintro ⟨f, hf⟩
  rw [LinearMap.zero_apply]
  refine Submodule.span_induction
    (p := fun (f : GL (Fin 3) F → ℂ) (hf : f ∈ gl3CyclicSubspace W) => M ⟨f, hf⟩ = 0) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨g, rfl⟩
    exact hgen g
  · exact M.map_zero
  · intro a b ha hb h₁ h₂
    change M (⟨a, ha⟩ + ⟨b, hb⟩) = 0
    rw [map_add, h₁, h₂, add_zero]
  · intro r a ha h₁
    change M (r • ⟨a, ha⟩) = 0
    rw [map_smul, h₁, smul_zero]

private theorem hasWhittakerMultOne_of_transport_vanishing (ψ : AddChar F ℂ) (W : GL (Fin 3) F → ℂ)
    (hW : IsGL3PsiWhittakerFn ψ W) (hW1 : W 1 = 1)
    (hV : ∀ L : gl3CyclicSubspace W →ₗ[ℂ] ℂ, IsGL3WhittakerFunctional (gl3CyclicRep W) ψ L →
      L (cyclicGenerator W) = 0 → whittakerFnOfFunctional W L = 0) : HasWhittakerMultOne ψ W := by
  unfold HasWhittakerMultOne GL3WhittakerUniquenessStatement
  haveI : Module.Free ℂ (gl3WhittakerFunctionalSpace (gl3CyclicRep W) ψ) := Module.Free.of_divisionRing ℂ _
  rw [rank_submodule_le_one_iff' (gl3WhittakerFunctionalSpace (gl3CyclicRep W) ψ)]
  refine ⟨evalOneOnCyclic W, fun L hL => ?_⟩
  have hLw : IsGL3WhittakerFunctional (gl3CyclicRep W) ψ L := hL
  have hev : IsGL3WhittakerFunctional (gl3CyclicRep W) ψ (evalOneOnCyclic W) :=
    isGL3WhittakerFunctional_evalOneOnCyclic ψ W hW
  have hM : IsGL3WhittakerFunctional (gl3CyclicRep W) ψ (L - L (cyclicGenerator W) • evalOneOnCyclic W) :=
    Submodule.sub_mem (gl3WhittakerFunctionalSpace (gl3CyclicRep W) ψ) hLw
      (Submodule.smul_mem (gl3WhittakerFunctionalSpace (gl3CyclicRep W) ψ) _ hev)
  have hM1 : (L - L (cyclicGenerator W) • evalOneOnCyclic W) (cyclicGenerator W) = 0 := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    show L (cyclicGenerator W) - L (cyclicGenerator W) * W 1 = 0
    rw [hW1, mul_one, sub_self]
  have hzero := eq_zero_of_whittakerFnOfFunctional_eq_zero W _ (hV _ hM hM1)
  rw [Submodule.mem_span_singleton]
  exact ⟨L (cyclicGenerator W), (sub_eq_zero.mp hzero).symm⟩

private theorem hasWhittakerMultOne_of_vanishing (ψ : AddChar F ℂ) (W : GL (Fin 3) F → ℂ)
    (hW : IsGL3PsiWhittakerFn ψ W) (hW1 : W 1 = 1) (P : (GL (Fin 3) F → ℂ) → Prop)
    (hP : ∀ L : gl3CyclicSubspace W →ₗ[ℂ] ℂ, IsGL3WhittakerFunctional (gl3CyclicRep W) ψ L →
      P (whittakerFnOfFunctional W L))
    (hvan : ∀ W' : GL (Fin 3) F → ℂ, P W' → W' 1 = 0 → W' = 0) : HasWhittakerMultOne ψ W :=
  hasWhittakerMultOne_of_transport_vanishing ψ W hW hW1 fun L hL h0 =>
    hvan _ (hP L hL) (by rw [whittakerFnOfFunctional_one]; exact h0)

end Transport

section Spherical

private theorem centralGen_mul_comm (v : HeightOneSpectrum (𝓞 ℚ)) (h : LocalGL3 v) :
    centralGen v * h = h * centralGen v := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have hdiag : (centralGen v : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.scalar (Fin 3) (varpi v) := by
    rw [Matrix.scalar_apply]
    show Matrix.diagonal ![varpi v, varpi v, varpi v] = Matrix.diagonal fun _ => varpi v
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hdiag]
  exact (Matrix.scalar_commute (varpi v) (fun r => Commute.all _ r)
    (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))).eq

private theorem hasWhittakerMultOne_of_vanishing_of_isCosetEigenfunction (v : HeightOneSpectrum (𝓞 ℚ))
    (U : Subgroup (LocalGL3 v)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (l₁ l₂ e₃ : ℂ) (W : LocalGL3 v → ℂ)
    (hU : IsRightInvariant U W) (hT₁ : IsCosetEigenfunction U (heckeGen1 v) W l₁)
    (hT₂ : IsCosetEigenfunction U (heckeGen2 v) W l₂) (hZ : ∀ g, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn ψv W) (hW1 : W 1 = 1)
    (hvan : ∀ W' : LocalGL3 v → ℂ, IsRightInvariant U W' → IsCosetEigenfunction U (heckeGen1 v) W' l₁ →
      IsCosetEigenfunction U (heckeGen2 v) W' l₂ → (∀ g, W' (centralGen v * g) = e₃ * W' g) →
      IsGL3PsiWhittakerFn ψv W' → W' 1 = 0 → W' = 0) :
    HasWhittakerMultOne ψv W :=
  hasWhittakerMultOne_of_vanishing ψv W hψ hW1
    (fun W' => IsRightInvariant U W' ∧ IsCosetEigenfunction U (heckeGen1 v) W' l₁ ∧
      IsCosetEigenfunction U (heckeGen2 v) W' l₂ ∧ (∀ g, W' (centralGen v * g) = e₃ * W' g) ∧
      IsGL3PsiWhittakerFn ψv W')
    (fun L hL => ⟨isRightInvariant_whittakerFnOfFunctional U W hU L,
      isCosetEigenfunction_whittakerFnOfFunctional U (heckeGen1 v) W l₁ hT₁ L,
      isCosetEigenfunction_whittakerFnOfFunctional U (heckeGen2 v) W l₂ hT₂ L,
      whittakerFnOfFunctional_central_mul W (centralGen v) (centralGen_mul_comm v) e₃ hZ L,
      isGL3PsiWhittakerFn_whittakerFnOfFunctional ψv W L hL⟩)
    (fun W' h h0 => hvan W' h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 h0)

end Spherical

section Closure

variable {G : Type*} [Group G]

private theorem isRightInvariant_add (U : Subgroup G) {W₁ W₂ : G → ℂ} (h₁ : IsRightInvariant U W₁)
    (h₂ : IsRightInvariant U W₂) : IsRightInvariant U (W₁ + W₂) := by
  intro g u hu
  simp only [Pi.add_apply, h₁ g u hu, h₂ g u hu]

private theorem isCosetEigenfunction_add (U : Subgroup G) (gen : G) {W₁ W₂ : G → ℂ} {lam : ℂ}
    (h₁ : IsCosetEigenfunction U gen W₁ lam) (h₂ : IsCosetEigenfunction U gen W₂ lam) :
    IsCosetEigenfunction U gen (W₁ + W₂) lam := by
  intro ι _ reps hreps g
  have e₁ := h₁ ι reps hreps g
  have e₂ := h₂ ι reps hreps g
  simp only [cosetSum] at e₁ e₂ ⊢
  simp only [Pi.add_apply, Finset.sum_add_distrib, e₁, e₂, mul_add]

private theorem central_law_add (z : G) {e : ℂ} {W₁ W₂ : G → ℂ} (h₁ : ∀ g, W₁ (z * g) = e * W₁ g)
    (h₂ : ∀ g, W₂ (z * g) = e * W₂ g) : ∀ g, (W₁ + W₂) (z * g) = e * (W₁ + W₂) g := by
  intro g
  simp only [Pi.add_apply, h₁ g, h₂ g, mul_add]

end Closure

section ClosureLaw

variable {F : Type*} [CommRing F] {R : Type*} [CommRing R]

private theorem isGL3PsiWhittakerFn_add (ψ : AddChar F R) {W₁ W₂ : GL (Fin 3) F → R} (h₁ : IsGL3PsiWhittakerFn ψ W₁)
    (h₂ : IsGL3PsiWhittakerFn ψ W₂) : IsGL3PsiWhittakerFn ψ (W₁ + W₂) :=
  (gl3PsiWhittakerFnSpace F R ψ).add_mem h₁ h₂

end ClosureLaw

section Level

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem upperUnipotent3_mem_localMaximalCompact3 {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ 1) :
    upperUnipotent3 x 0 0 ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [mem_localMaximalCompact3_iff]
  refine ⟨?_, ?_⟩
  · intro i j
    rw [upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp [hx]
  · intro i j
    show Valued.v ((!![1, -x, x * 0 - 0; 0, 1, -0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [hx]

private theorem addChar_apply_eq_one_of_valued_le_one {ψv : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ}
    (hψ : IsGL3PsiWhittakerFn ψv W) (hU : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hW1 : W 1 = 1) {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ 1) : ψv x = 1 := by
  have h₁ := hψ x 0 0 1
  have h₂ := hU 1 (upperUnipotent3 x 0 0) (upperUnipotent3_mem_localMaximalCompact3 v hx)
  rw [mul_one, hW1, add_zero, mul_one] at h₁
  rw [one_mul, hW1] at h₂
  rw [← h₁, h₂]

private theorem exists_valued_le_one_and_apply_inv_varpi_mul_ne_one {ψv : AddChar (v.adicCompletion ℚ) ℂ}
    (hlev : addCharLevel ψv = 0) (hne : ψv ≠ 1) :
    ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1 := by
  have hlevS : sSup {n : ℤ | ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → ψv x = 1} = 0 := hlev
  set S : Set ℤ := {n : ℤ | ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → ψv x = 1} with hS

  have hbdd : BddAbove S := by
    by_contra hnb
    apply hne
    refine AddChar.ext ψv 1 fun y => ?_
    rw [AddChar.one_apply]
    by_cases hy : y = 0
    · subst hy
      exact AddChar.map_zero_eq_one ψv
    · have hvy : Valued.v y ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hy
      obtain ⟨n, hnS, hmn⟩ := not_bddAbove_iff.mp hnb (WithZero.log (Valued.v y))
      simp only [hS, Set.mem_setOf_eq] at hnS
      refine hnS y ?_
      rw [← WithZero.exp_log hvy]
      exact WithZero.exp_le_exp.mpr hmn.le

  have h1 : (1 : ℤ) ∉ S := by
    intro h1
    have := le_csSup hbdd h1
    rw [hlevS] at this
    exact absurd this (by norm_num)
  simp only [hS, Set.mem_setOf_eq, not_forall] at h1
  obtain ⟨y, hy, hy1⟩ := h1
  refine ⟨varpi v * y, ?_, ?_⟩
  · have hϖ : Valued.v (varpi v) = WithZero.exp (-1 : ℤ) := valued_uniformizerUnit ℚ v
    calc Valued.v (varpi v * y) = Valued.v (varpi v) * Valued.v y := Valuation.map_mul _ _ _
      _ ≤ WithZero.exp (-1 : ℤ) * WithZero.exp (1 : ℤ) := by
          rw [hϖ]
          exact mul_le_mul_right hy _
      _ = 1 := by
          rw [← WithZero.exp_add]
          norm_num
  · rw [inv_mul_cancel_left₀ (varpi_ne_zero v)]
    exact hy1

end Level

section CentralPowers

variable {G : Type*} [Group G]

private theorem eq_zero_of_central_law_zero (z : G) {W : G → ℂ} (hZ : ∀ g, W (z * g) = 0 * W g) : W = 0 := by
  funext h
  have := hZ (z⁻¹ * h)
  rw [mul_inv_cancel_left, zero_mul] at this
  rw [this, Pi.zero_apply]

private theorem ne_zero_of_central_law_of_apply_one_eq_one (z : G) {e : ℂ} {W : G → ℂ}
    (hZ : ∀ g, W (z * g) = e * W g) (hW1 : W 1 = 1) : e ≠ 0 := by
  rintro rfl
  rw [eq_zero_of_central_law_zero z hZ, Pi.zero_apply] at hW1
  exact zero_ne_one hW1

end CentralPowers

section Vanish

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem eq_zero_of_apply_one_eq_zero_of_local_laws (ψv : AddChar (v.adicCompletion ℚ) ℂ) (e₁ e₂ e₃ : ℂ)
    (A : ℕ → ℂ) (B : ℕ → ℕ → ℂ)
    (uniq : ∀ W : LocalGL3 v → ℂ,
      (IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
        IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
        IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
        ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) →
      IsGL3PsiWhittakerFn ψv W → (∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1) →
      W 1 = 1 →
      (∀ n : ℕ, W (iotaTorusLocal v n) = A n) ∧
        ∀ k₁ k₂ : ℕ, k₂ + 1 ≤ k₁ → W (twoRowPointLocal v k₁ (k₂ + 1)) = B k₁ k₂)
    (supp : ∀ W : LocalGL3 v → ℂ, IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W →
      IsGL3PsiWhittakerFn ψv W → (∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1) →
      ∀ (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ),
        (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d →
        Valued.v (d 1) < Valued.v (d 0) ∨ Valued.v (d 2) < Valued.v (d 1) → W t = 0)
    (decomp : ∀ g : LocalGL3 v,
      ∃ (x y z : v.adicCompletion ℚ) (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ),
        ∃ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
          (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d ∧
            g = upperUnipotent3 x y z * t * k)
    (norm : ∀ W : LocalGL3 v → ℂ, IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W →
      (∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) →
      ∀ (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ),
        (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d →
        ∀ (k₁ k₂ : ℕ) (c : ℤ), Valued.v (d 0) = WithZero.exp (-((k₁ : ℤ) + c)) →
          Valued.v (d 1) = WithZero.exp (-((k₂ : ℤ) + c)) → Valued.v (d 2) = WithZero.exp (-c) →
          W t = e₃ ^ c * W (twoRowPointLocal v k₁ k₂))
    (shape : ∀ (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ),
      (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d →
      ¬ (Valued.v (d 1) < Valued.v (d 0) ∨ Valued.v (d 2) < Valued.v (d 1)) →
      ∃ (k₁ k₂ : ℕ) (c : ℤ), Valued.v (d 0) = WithZero.exp (-((k₁ : ℤ) + c)) ∧
        Valued.v (d 1) = WithZero.exp (-((k₂ : ℤ) + c)) ∧ Valued.v (d 2) = WithZero.exp (-c))
    {W : LocalGL3 v → ℂ}
    (hU : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hT₁ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁))
    (hT₂ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂))
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) (hψ : IsGL3PsiWhittakerFn ψv W)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1) (hW1 : W 1 = 1) :
    ∀ W' : LocalGL3 v → ℂ,
      IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W' →
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W' (cNormQ v * e₁) →
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W' (cNormQ v * e₂) →
      (∀ g : LocalGL3 v, W' (centralGen v * g) = e₃ * W' g) →
      IsGL3PsiWhittakerFn ψv W' → W' 1 = 0 → W' = 0 := by
  intro W' hU' hT₁' hT₂' hZ' hψ' hW'1

  obtain ⟨hA, hB⟩ := uniq W ⟨hU, hT₁, hT₂, hZ⟩ hψ hψ1 hW1
  have hsum1 : (W + W') 1 = 1 := by
    rw [Pi.add_apply, hW1, hW'1, add_zero]
  obtain ⟨hA', hB'⟩ := uniq (W + W')
    ⟨isRightInvariant_add _ hU hU', isCosetEigenfunction_add _ _ hT₁ hT₁',
      isCosetEigenfunction_add _ _ hT₂ hT₂', central_law_add _ hZ hZ'⟩
    (isGL3PsiWhittakerFn_add ψv hψ hψ') hψ1 hsum1
  have hpt : ∀ k₁ k₂ : ℕ, k₂ ≤ k₁ → W' (twoRowPointLocal v k₁ k₂) = 0 := by
    intro k₁ k₂ hk
    cases k₂ with
    | zero =>
      have h₁ := hA k₁
      have h₂ := hA' k₁
      rw [Pi.add_apply] at h₂
      rw [twoRowPointLocal_zero_right]
      linear_combination h₂ - h₁
    | succ j =>
      have h₁ := hB k₁ j hk
      have h₂ := hB' k₁ j hk
      rw [Pi.add_apply] at h₂
      linear_combination h₂ - h₁

  funext g
  obtain ⟨x, y, z, t, d, k, hk, ht, rfl⟩ := decomp g
  have hg : W' (upperUnipotent3 x y z * t * k) = ψv (x + y) * W' t := by
    rw [hU' _ k hk, hψ' x y z t]
  rw [Pi.zero_apply, hg]
  by_cases hd : Valued.v (d 1) < Valued.v (d 0) ∨ Valued.v (d 2) < Valued.v (d 1)
  · rw [supp W' hU' hψ' hψ1 t d ht hd, mul_zero]
  · obtain ⟨k₁, k₂, c, h0, h1, h2⟩ := shape t d ht hd
    have hk₂ : k₂ ≤ k₁ := by
      have hle : Valued.v (d 0) ≤ Valued.v (d 1) := not_lt.mp fun h => hd (Or.inl h)
      rw [h0, h1, WithZero.exp_le_exp] at hle
      omega
    rw [norm W' hU' hZ' t d ht k₁ k₂ c h0 h1 h2, hpt k₁ k₂ hk₂, mul_zero, mul_zero]

end Vanish

private theorem sphericalTorusValue_eq_of_apply_one_eq_one
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
      ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn ψv W)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1) (hW1 : W 1 = 1) :
    (∀ n : ℕ, W (iotaTorusLocal v n) = (cNormQ v)⁻¹ ^ n * sphericalTorusValue e₁ e₂ e₃ n) ∧
    (∀ k₁ k₂ : ℕ, k₂ + 1 ≤ k₁ → W (twoRowPointLocal v k₁ (k₂ + 1)) =
      (cNormQ v)⁻¹ ^ k₁ *
        (sphericalTorusValue e₁ e₂ e₃ k₁ * sphericalTorusValue e₁ e₂ e₃ (k₂ + 1) -
          sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) * sphericalTorusValue e₁ e₂ e₃ k₂)) := by
  have h := sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn v ψv W e₁ e₂ e₃ hW hψ
    (fun _ hx => addChar_apply_eq_one_of_valued_le_one v hψ hW.1 hW1 hx) hψ1
  simp only [hW1, one_mul] at h
  exact h

private theorem hasWhittakerMultOne_of_uniqueness_inputs (v : HeightOneSpectrum (𝓞 ℚ))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ) (e₁ e₂ e₃ : ℂ) (W : LocalGL3 v → ℂ)
    (uniq : ∀ W : LocalGL3 v → ℂ,
      (IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
        IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
        IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
        ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) →
      IsGL3PsiWhittakerFn ψv W → (∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1) →
      W 1 = 1 →
      (∀ n : ℕ, W (iotaTorusLocal v n) = (cNormQ v)⁻¹ ^ n * sphericalTorusValue e₁ e₂ e₃ n) ∧
        ∀ k₁ k₂ : ℕ, k₂ + 1 ≤ k₁ → W (twoRowPointLocal v k₁ (k₂ + 1)) =
          (cNormQ v)⁻¹ ^ k₁ *
            (sphericalTorusValue e₁ e₂ e₃ k₁ * sphericalTorusValue e₁ e₂ e₃ (k₂ + 1) -
              sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) * sphericalTorusValue e₁ e₂ e₃ k₂))
    (supp : ∀ W : LocalGL3 v → ℂ, IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W →
      IsGL3PsiWhittakerFn ψv W → (∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1) →
      ∀ (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ),
        (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d →
        Valued.v (d 1) < Valued.v (d 0) ∨ Valued.v (d 2) < Valued.v (d 1) → W t = 0)
    (decomp : ∀ g : LocalGL3 v,
      ∃ (x y z : v.adicCompletion ℚ) (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ),
        ∃ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
          (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d ∧
            g = upperUnipotent3 x y z * t * k)
    (norm : ∀ W : LocalGL3 v → ℂ, IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W →
      (∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) →
      ∀ (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ),
        (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d →
        ∀ (k₁ k₂ : ℕ) (c : ℤ), Valued.v (d 0) = WithZero.exp (-((k₁ : ℤ) + c)) →
          Valued.v (d 1) = WithZero.exp (-((k₂ : ℤ) + c)) → Valued.v (d 2) = WithZero.exp (-c) →
          W t = e₃ ^ c * W (twoRowPointLocal v k₁ k₂))
    (shape : ∀ (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ),
      (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d →
      ¬ (Valued.v (d 1) < Valued.v (d 0) ∨ Valued.v (d 2) < Valued.v (d 1)) →
      ∃ (k₁ k₂ : ℕ) (c : ℤ), Valued.v (d 0) = WithZero.exp (-((k₁ : ℤ) + c)) ∧
        Valued.v (d 1) = WithZero.exp (-((k₂ : ℤ) + c)) ∧ Valued.v (d 2) = WithZero.exp (-c))
    (hU : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hT₁ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁))
    (hT₂ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂))
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn ψv W) (hlev : LanglandsTunnell.TateLocal.addCharLevel ψv = 0) (hne : ψv ≠ 1)
    (hW1 : W 1 = 1) :
    HasWhittakerMultOne ψv W :=
  hasWhittakerMultOne_of_vanishing_of_isCosetEigenfunction v _ ψv _ _ e₃ W hU hT₁ hT₂ hZ hψ hW1
    (eq_zero_of_apply_one_eq_zero_of_local_laws v ψv e₁ e₂ e₃ _ _ uniq supp decomp norm shape hU hT₁ hT₂ hZ hψ
      (exists_valued_le_one_and_apply_inv_varpi_mul_ne_one v hlev hne) hW1)

end SphericalWhittakerRigidity

end

open LanglandsTunnell.CubicInduction in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (e₁ e₂ e₃ : ℂ) (W : LocalGL3 v → ℂ)
    (hU : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hT₁ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁))
    (hT₂ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂))
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn ψv W) (hlev : LanglandsTunnell.TateLocal.addCharLevel ψv = 0) (hne : ψv ≠ 1)
    (hW1 : W 1 = 1) :
    HasWhittakerMultOne ψv W :=
  SphericalWhittakerRigidity.hasWhittakerMultOne_of_uniqueness_inputs v ψv e₁ e₂ e₃ W
    (fun W' => SphericalWhittakerRigidity.sphericalTorusValue_eq_of_apply_one_eq_one v ψv W' e₁ e₂ e₃)
    (eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn v ψv)
    (exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 v)
    (fun W' => eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant v W' e₃)
    (exists_valued_eq_exp_of_coe_eq_diagonal_of_not_valued_lt v) hU hT₁ hT₂ hZ hψ hlev hne hW1

end S_LanglandsTunnell_CubicInduction_hasWhittakerMultOne_of_isCosetEigenfunction
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_hasWhittakerMultOne_of_isCosetEigenfunction (solution)
