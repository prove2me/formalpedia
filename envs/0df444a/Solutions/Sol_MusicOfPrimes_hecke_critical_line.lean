-- Prove2me | solution 1 for MusicOfPrimes.hecke_critical_line
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T21:52:33.026013+00:00
-- url     : https://prove2.me/submissions/6aa52471-61c8-4d2c-b37c-cb5ae04f99c1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MusicOfPrimes_HeckeL
import Theorems.Thm_MusicOfPrimes_hecke_grh
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Theorems.Thm_NumberField_TateGlobal_exists_forall_prod_Gamma_mul_eulerProduct_one_sub_eq_mul_cpow_mul_of_archLocalChar_eq
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous

/-!
# The critical-line form of GRH for completed Hecke L-functions follows from the half-plane form

`solution` derives `MusicOfPrimes.hecke_critical_line` from `MusicOfPrimes.hecke_grh` (the
zero-free half-plane `Re s > 1/2` for the finite Hecke L-functions) by the functional equation.
The first part treats the powers of the idelic norm (completed Dedekind zeta function), the second
part the remaining characters (Tate's functional equation for `χ` and `χ⁻¹`).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal Complex
open scoped Classical BigOperators

noncomputable section

namespace MusicOfPrimes.CL

/-!
# The norm-power branch

For `χ = |·|^{iτ}` the completed L-function is, up to a nowhere vanishing factor, the completed
Dedekind zeta function at `s + iτ`, and the finite L-function is the continued Dedekind zeta
function at `s + iτ`.  The two are compared on `{Re > 1/2} \ {1}` by the identity theorem, and the
left half-plane is reached by the symmetry `Λ(1 - z) = Λ(z)`.
-/

variable (F : Type) [Field F] [NumberField F]

/-! ### Additivity of `t ↦ |·|^{it}` -/

theorem normPowChar_add (a b : ℝ) :
    normPowChar F (a + b) = normPowChar F a * normPowChar F b := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [MonoidHom.mul_apply, Units.val_mul, coe_normPowChar_apply, coe_normPowChar_apply,
    coe_normPowChar_apply, ofReal_add, mul_add,
    cpow_add _ _ (ofReal_ne_zero.mpr (ideleNorm_pos x).ne')]

theorem normPowChar_neg (a : ℝ) : normPowChar F (-a) = (normPowChar F a)⁻¹ := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, coe_normPowChar_apply,
    coe_normPowChar_apply, ofReal_neg, mul_neg, cpow_neg]

/-- `Γ_ℂ` has no zero in the right half-plane. -/
theorem Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [Gammaℂ_def]
  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact mul_ne_zero (mul_ne_zero two_ne_zero fun h => h2π ((cpow_eq_zero_iff _ _).mp h).1)
    (Gamma_ne_zero_of_re_pos hs)

/-! ### The two Dedekind functions of the definition file -/

theorem dedekindCompleted_spec :
    DifferentiableOn ℂ (dedekindCompleted F) ({(0 : ℂ), 1}ᶜ) ∧
    (∀ s : ℂ, s ≠ 0 → s ≠ 1 → dedekindCompleted F (1 - s) = dedekindCompleted F s) ∧
    (∀ s : ℂ, 1 < s.re → dedekindCompleted F s =
      (((|NumberField.discr F| : ℤ) : ℂ)) ^ (s / 2)
        * Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces F
        * Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F
        * NumberField.dedekindZeta F s) := by
  have h := Classical.choose_spec (NumberField.exists_completedDedekindZeta_package F)
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem dedekindZetaCont_spec :
    DifferentiableOn ℂ (dedekindZetaCont F) ({s : ℂ | 1 / 2 < s.re} \ {1}) ∧
    (∀ s : ℂ, 1 < s.re →
      dedekindZetaCont F s =
        ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F)))},
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) := by
  have h := Classical.choose_spec
    (NumberField.exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul
      F ∅)
  exact ⟨h.1, h.2.1⟩

theorem zetaCont_eq_dedekindZeta {z : ℂ} (hz : 1 < z.re) :
    dedekindZetaCont F z = NumberField.dedekindZeta F z := by
  rw [(dedekindZetaCont_spec F).2 z hz,
    ← (NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta F z hz).tprod_eq]
  let e : {v : HeightOneSpectrum (𝓞 F) // v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F)))} ≃
      HeightOneSpectrum (𝓞 F) := Equiv.subtypeUnivEquiv (fun v => Finset.notMem_empty v)
  exact e.tprod_eq
    (fun v : HeightOneSpectrum (𝓞 F) => (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z))⁻¹)

/-! ### The archimedean factor of the Dedekind zeta function -/

/-- `|d_F|^{z/2} Γ_ℝ(z)^{r₁} Γ_ℂ(z)^{r₂}`. -/
def G (z : ℂ) : ℂ :=
  (((|NumberField.discr F| : ℤ) : ℂ)) ^ (z / 2)
    * Gammaℝ z ^ NumberField.InfinitePlace.nrRealPlaces F
    * Gammaℂ z ^ NumberField.InfinitePlace.nrComplexPlaces F

/-- The entire function which is the inverse of `G` wherever `G` does not vanish. -/
def Ginv (z : ℂ) : ℂ :=
  ((((|NumberField.discr F| : ℤ) : ℂ)) ^ (z / 2))⁻¹
    * ((Gammaℝ z)⁻¹) ^ NumberField.InfinitePlace.nrRealPlaces F
    * ((Gammaℂ z)⁻¹) ^ NumberField.InfinitePlace.nrComplexPlaces F

theorem discr_cast_ne_zero : (((|NumberField.discr F| : ℤ) : ℂ)) ≠ 0 := by
  exact_mod_cast abs_ne_zero.mpr (NumberField.discr_ne_zero F)

theorem discr_cpow_ne_zero (z : ℂ) : (((|NumberField.discr F| : ℤ) : ℂ)) ^ z ≠ 0 := fun h =>
  discr_cast_ne_zero F ((cpow_eq_zero_iff _ _).mp h).1

theorem G_ne_zero {z : ℂ} (hz : 0 < z.re) : G F z ≠ 0 :=
  mul_ne_zero (mul_ne_zero (discr_cpow_ne_zero F _)
    (pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos hz))) (pow_ne_zero _ (Gammaℂ_ne_zero_of_re_pos hz))

theorem G_mul_Ginv {z : ℂ} (hz : 0 < z.re) : G F z * Ginv F z = 1 := by
  have e : Ginv F z = (G F z)⁻¹ := by
    unfold G Ginv
    rw [inv_pow, inv_pow, mul_inv, mul_inv]
  rw [e, mul_inv_cancel₀ (G_ne_zero F hz)]

theorem differentiable_Ginv : Differentiable ℂ (Ginv F) := by
  intro z
  have h1 : DifferentiableAt ℂ
      (fun z : ℂ => (((|NumberField.discr F| : ℤ) : ℂ)) ^ (z / 2)) z :=
    (differentiableAt_id.div_const 2).const_cpow (Or.inl (discr_cast_ne_zero F))
  have h2 : DifferentiableAt ℂ
      (fun z : ℂ => ((((|NumberField.discr F| : ℤ) : ℂ)) ^ (z / 2))⁻¹) z :=
    h1.inv (discr_cpow_ne_zero F _)
  exact (h2.mul ((differentiable_Gammaℝ_inv z).pow _)).mul ((differentiable_Gammaℂ_inv z).pow _)

/-! ### Comparison on `{Re > 1/2} \ {1}` -/

/-- The completed Dedekind zeta function divided by its archimedean factor. -/
def LG (w : ℂ) : ℂ := dedekindCompleted F w * Ginv F w

theorem LG_eq_of_one_lt {w : ℂ} (hw : 1 < w.re) : LG F w = dedekindZetaCont F w := by
  have hG := G_mul_Ginv F (by linarith : 0 < w.re)
  unfold G at hG
  rw [zetaCont_eq_dedekindZeta F hw]
  unfold LG
  rw [(dedekindCompleted_spec F).2.2 w hw]
  linear_combination (NumberField.dedekindZeta F w) * hG

theorem strip_subset :
    ({s : ℂ | 1 / 2 < s.re} \ {1} : Set ℂ) ⊆ ({(0 : ℂ), 1}ᶜ : Set ℂ) := by
  intro w hw
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  refine ⟨fun h0 => ?_, fun h1 => hw.2 (Set.mem_singleton_iff.mpr h1)⟩
  have h := hw.1
  rw [Set.mem_setOf_eq, h0, Complex.zero_re] at h
  linarith

theorem LG_differentiableOn :
    DifferentiableOn ℂ (LG F) ({s : ℂ | 1 / 2 < s.re} \ {1}) :=
  (((dedekindCompleted_spec F).1).mono (strip_subset)).mul
    (differentiable_Ginv F).differentiableOn

theorem eqOn_piece (U : Set ℂ) (z₀ : ℂ) (hUW : U ⊆ ({s : ℂ | 1 / 2 < s.re} \ {1} : Set ℂ))
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hz₀ : z₀ ∈ U)
    (h : LG F =ᶠ[nhds z₀] dedekindZetaCont F) : Set.EqOn (LG F) (dedekindZetaCont F) U :=
  (((LG_differentiableOn F).mono hUW).analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    ((((dedekindZetaCont_spec F).1).mono hUW).analyticOnNhd hUo) hUc.isPreconnected hz₀ h

theorem eventuallyEq_of_one_lt {z₀ : ℂ} (h0 : 1 < z₀.re) :
    LG F =ᶠ[nhds z₀] dedekindZetaCont F :=
  Filter.eventuallyEq_of_mem
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds h0)
    (fun w hw => LG_eq_of_one_lt F hw)

theorem LG_eq_upper :
    Set.EqOn (LG F) (dedekindZetaCont F) ({w : ℂ | 1 / 2 < w.re} ∩ {w : ℂ | 0 < w.im}) := by
  refine eqOn_piece F _ (2 + I) ?_
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im))
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt _)) ?_
    (eventuallyEq_of_one_lt F ?_)
  · intro w hw
    refine ⟨hw.1, fun h => ?_⟩
    have h2 := hw.2
    rw [Set.mem_singleton_iff.mp h, Set.mem_setOf_eq, Complex.one_im] at h2
    exact lt_irrefl _ h2
  · constructor
    · show (1 / 2 : ℝ) < (2 + I).re
      rw [Complex.add_re, Complex.I_re]; norm_num
    · show (0 : ℝ) < (2 + I).im
      rw [Complex.add_im, Complex.I_im]; norm_num
  · rw [Complex.add_re, Complex.I_re]; norm_num

theorem LG_eq_lower :
    Set.EqOn (LG F) (dedekindZetaCont F) ({w : ℂ | 1 / 2 < w.re} ∩ {w : ℂ | w.im < 0}) := by
  refine eqOn_piece F _ (2 - I) ?_
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_im continuous_const))
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_lt _)) ?_
    (eventuallyEq_of_one_lt F ?_)
  · intro w hw
    refine ⟨hw.1, fun h => ?_⟩
    have h2 := hw.2
    rw [Set.mem_singleton_iff.mp h, Set.mem_setOf_eq, Complex.one_im] at h2
    exact lt_irrefl _ h2
  · constructor
    · show (1 / 2 : ℝ) < (2 - I).re
      rw [Complex.sub_re, Complex.I_re]; norm_num
    · show (2 - I).im < (0 : ℝ)
      rw [Complex.sub_im, Complex.I_im]; norm_num
  · rw [Complex.sub_re, Complex.I_re]; norm_num

theorem LG_eq_strip :
    Set.EqOn (LG F) (dedekindZetaCont F) ({w : ℂ | 1 / 2 < w.re} ∩ {w : ℂ | w.re < 1}) := by
  have hmem : ((3 / 4 : ℂ) + I) ∈ ({w : ℂ | 1 / 2 < w.re} ∩ {w : ℂ | 0 < w.im} : Set ℂ) := by
    constructor
    · show (1 / 2 : ℝ) < ((3 / 4 : ℂ) + I).re
      rw [Complex.add_re, Complex.I_re]; norm_num
    · show (0 : ℝ) < ((3 / 4 : ℂ) + I).im
      rw [Complex.add_im, Complex.I_im]; norm_num
  refine eqOn_piece F _ ((3 / 4 : ℂ) + I) ?_
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const))
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)) ?_
    (Filter.eventuallyEq_of_mem
      (((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt continuous_const Complex.continuous_im)).mem_nhds hmem) (LG_eq_upper F))
  · intro w hw
    refine ⟨hw.1, fun h => ?_⟩
    have h2 := hw.2
    rw [Set.mem_singleton_iff.mp h, Set.mem_setOf_eq, Complex.one_re] at h2
    exact lt_irrefl _ h2
  · constructor
    · exact hmem.1
    · show ((3 / 4 : ℂ) + I).re < (1 : ℝ)
      rw [Complex.add_re, Complex.I_re]; norm_num

/-- On `{Re > 1/2} \ {1}` the completed Dedekind zeta function divided by its archimedean factor
is the continued Dedekind zeta function. -/
theorem completed_mul_Ginv_eq {z : ℂ} (hz : 1 / 2 < z.re) (hz1 : z ≠ 1) :
    dedekindCompleted F z * Ginv F z = dedekindZetaCont F z := by
  show LG F z = dedekindZetaCont F z
  rcases lt_trichotomy z.im 0 with him | him | him
  · exact LG_eq_lower F ⟨hz, him⟩
  · have hre : z.re ≠ 1 := fun h =>
      hz1 (Complex.ext (h.trans Complex.one_re.symm) (him.trans Complex.one_im.symm))
    rcases lt_or_gt_of_ne hre with h | h
    · exact LG_eq_strip F ⟨hz, h⟩
    · exact LG_eq_of_one_lt F h
  · exact LG_eq_upper F ⟨hz, him⟩

theorem dedekindCompleted_eq {z : ℂ} (hz : 1 / 2 < z.re) (hz1 : z ≠ 1) :
    dedekindCompleted F z = G F z * dedekindZetaCont F z := by
  have hG := G_mul_Ginv F (by linarith : 0 < z.re)
  rw [← completed_mul_Ginv_eq F hz hz1]
  linear_combination (-dedekindCompleted F z) * hG

theorem dedekindCompleted_ne_zero {w : ℂ} (hw : 1 / 2 < w.re) (hw1 : w ≠ 1)
    (hZ : dedekindZetaCont F w ≠ 0) : dedekindCompleted F w ≠ 0 := fun hΛ =>
  hZ (by rw [← completed_mul_Ginv_eq F hw hw1, hΛ, zero_mul])

/-! ### The norm-power branch of the critical-line statement -/

theorem pow_branch
    (hgrh : ∀ (χ : HeckeChar F) (s : ℂ), (1 / 2 : ℝ) < s.re →
      ¬ (∃ τ₀ : ℝ, χ.toFun = normPowChar F τ₀ ∧ s = 1 - (τ₀ : ℂ) * I) →
      heckeLFin F χ s ≠ 0)
    (χ : HeckeChar F) (h : IsNormPowChar F χ) (s : ℂ) (hs : s.re ≠ 1 / 2)
    (hpole : ¬ (∃ τ₀ : ℝ, χ.toFun = normPowChar F τ₀ ∧
      (s = -(τ₀ : ℂ) * I ∨ s = 1 - (τ₀ : ℂ) * I))) :
    heckeLCompleted F χ s ≠ 0 := by
  obtain ⟨τ, hτeq⟩ : ∃ τ : ℝ, τ = normPowτ F χ h := ⟨_, rfl⟩
  have hτ : χ.toFun = normPowChar F τ := by
    rw [hτeq]
    exact normPowτ_spec F χ h
  have hLfin : ∀ w : ℂ, heckeLFin F χ w = dedekindZetaCont F (w + (τ : ℂ) * I) := by
    intro w
    rw [hτeq]
    unfold heckeLFin
    rw [dif_pos h]
  have hLc : heckeLCompleted F χ s =
      ((((|NumberField.discr F| : ℤ) : ℂ)) ^ ((s + (τ : ℂ) * I) / 2))⁻¹ *
        dedekindCompleted F (s + (τ : ℂ) * I) := by
    rw [hτeq]
    unfold heckeLCompleted
    rw [dif_pos h]
  have hzre : (s + (τ : ℂ) * I).re = s.re := by simp
  have hz1 : s + (τ : ℂ) * I ≠ 1 := fun e =>
    hpole ⟨τ, hτ, Or.inr (by linear_combination e)⟩
  have hz0 : s + (τ : ℂ) * I ≠ 0 := fun e =>
    hpole ⟨τ, hτ, Or.inl (by linear_combination e)⟩
  rw [hLc]
  refine mul_ne_zero (inv_ne_zero (discr_cpow_ne_zero F _)) ?_
  rcases lt_or_gt_of_ne hs with hlt | hgt
  · rw [← (dedekindCompleted_spec F).2.1 (s + (τ : ℂ) * I) hz0 hz1]
    have hre' : (1 - (s + (τ : ℂ) * I)).re = 1 - s.re := by simp
    apply dedekindCompleted_ne_zero F
    · rw [hre']; linarith
    · intro e
      exact hz0 (by linear_combination -e)
    · have e : (1 - (s + (τ : ℂ) * I)) = (1 - s - 2 * (τ : ℂ) * I) + (τ : ℂ) * I := by ring
      rw [e, ← hLfin]
      apply hgrh
      · have hre'' : (1 - s - 2 * (τ : ℂ) * I).re = 1 - s.re := by simp
        rw [hre'']; linarith
      · rintro ⟨τ₀, h1, h2⟩
        apply hpole
        refine ⟨2 * τ - τ₀, ?_, Or.inl ?_⟩
        · have e1 : normPowChar F (2 * τ - τ₀) * normPowChar F τ₀ =
              normPowChar F τ * normPowChar F τ := by
            rw [← normPowChar_add, ← normPowChar_add]
            congr 1
            ring
          rw [← h1, ← hτ] at e1
          exact (mul_right_cancel e1).symm
        · push_cast
          linear_combination -h2
  · apply dedekindCompleted_ne_zero F (by rw [hzre]; exact hgt) hz1
    rw [← hLfin]
    exact hgrh χ s hgt (fun ⟨τ₀, h1, h2⟩ => hpole ⟨τ₀, h1, Or.inr h2⟩)

end MusicOfPrimes.CL

end

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal Complex
open scoped Classical BigOperators

noncomputable section

/-!
# The critical-line form of GRH for characters which are not norm powers

For a unitary Hecke character `χ` which is not a power of the idelic norm, the completed
function `Λ(s, χ)` is entire, equals `γ(s, χ) L_f(s, χ)` on `Re s > 0` and satisfies Tate's
functional equation `Λ(1 - s, χ⁻¹) = ε N^{s - 1/2} Λ(s, χ)`.  The zero-free half-plane for the
finite functions of `χ` and `χ⁻¹` therefore leaves no zero of `Λ(·, χ)` off the critical line.
-/

namespace MusicOfPrimes.CL

variable {F : Type} [Field F] [NumberField F]

/-- Two entire functions which agree on the half-plane `Re w > 1` are equal. -/
theorem entire_eq_of_eq_on_re_gt_one {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (h : ∀ w : ℂ, 1 < w.re → f w = g w) : f = g := by
  have hf' : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hg' : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : (2 : ℂ) ∈ {w : ℂ | 1 < w.re} := by
    show (1 : ℝ) < (2 : ℂ).re
    norm_num
  exact hf'.eq_of_eventuallyEq hg' (Filter.eventually_of_mem (hopen.mem_nhds h2) h)

/-- The archimedean factor has no zero in the right half-plane, whatever its parameters. -/
theorem gammaProd_ne_zero (τ : InfinitePlace F → ℝ) (m : InfinitePlace F → ℤ) (s : ℂ)
    (hs : 0 < s.re) :
    (∏ v : InfinitePlace F,
      (if v.IsReal then
        Gammaℝ (s + ((τ v : ℝ) : ℂ) * I + (((m v).natAbs % 2 : ℕ) : ℂ))
      else
        Gammaℂ (s + ((τ v : ℝ) : ℂ) * I + (((m v).natAbs : ℕ) : ℂ) / 2))) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun v _ => ?_
  split_ifs
  · refine Gammaℝ_ne_zero_of_re_pos ?_
    have h0 : (0 : ℝ) ≤ (((m v).natAbs % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, natCast_re, mul_zero, zero_mul,
      sub_zero, add_zero]
    linarith
  · refine Gammaℂ_ne_zero_of_re_pos ?_
    have h0 : (0 : ℝ) ≤ (((m v).natAbs : ℕ) : ℝ) / 2 := by positivity
    have h1 : ((((m v).natAbs : ℕ) : ℂ) / 2).re = (((m v).natAbs : ℕ) : ℝ) / 2 := by
      have h2 : ((((m v).natAbs : ℕ) : ℂ) / 2) = (((((m v).natAbs : ℕ) : ℝ) / 2 : ℝ) : ℂ) := by
        rw [ofReal_div, ofReal_natCast, ofReal_ofNat]
      rw [h2, ofReal_re]
    simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, h1, mul_zero, zero_mul,
      sub_zero, add_zero]
    linarith

/-- The inverse of a unitary Hecke character. -/
def invChar (χ : HeckeChar F) : HeckeChar F where
  toFun := χ.toFun⁻¹
  cont := (χ.cont.inv₀ fun z => Units.ne_zero _).congr fun z => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    rfl
  unitary := by
    intro x
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, χ.unitary x, inv_one]
  classChar := by
    intro u
    rw [MonoidHom.inv_apply, χ.classChar u, inv_one]

theorem invChar_apply (χ : HeckeChar F) (x : (AdeleRing (𝓞 F) F)ˣ) :
    (invChar χ).toFun x = (χ.toFun x)⁻¹ := rfl

theorem inv_invChar (χ : HeckeChar F) : ((invChar χ).toFun)⁻¹ = χ.toFun := inv_inv χ.toFun

theorem continuous_toFun (χ : HeckeChar F) : Continuous χ.toFun := by
  refine Units.continuous_iff.mpr ⟨χ.cont, ?_⟩
  exact (χ.cont.inv₀ fun z => Units.ne_zero _).congr fun z =>
    (Units.val_inv_eq_inv_val _).symm

theorem isUnramified_invChar (χ : HeckeChar F) (v : HeightOneSpectrum (𝓞 F)) :
    IsUnramifiedCharAt (invChar χ).toFun v ↔ IsUnramifiedCharAt χ.toFun v := by
  have key : ∀ t : (v.adicCompletion F)ˣ,
      localChar (invChar χ).toFun v t = (localChar χ.toFun v t)⁻¹ := fun t => rfl
  constructor
  · intro h t h1 h2
    have h3 := h t h1 h2
    rwa [key, inv_eq_one] at h3
  · intro h t h1 h2
    rw [key, h t h1 h2, inv_one]

theorem archLocalChar_invChar (χ : HeckeChar F) (v : InfinitePlace F) (x : (v.Completion)ˣ) :
    archLocalChar (invChar χ).toFun v x = (archLocalChar χ.toFun v x)⁻¹ := rfl

/-- The inverse of a norm power is the norm power with the opposite exponent. -/
theorem inv_normPowChar (τ₀ : ℝ) : (normPowChar F τ₀)⁻¹ = normPowChar F (-τ₀) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, coe_normPowChar_apply,
    coe_normPowChar_apply, ofReal_neg, mul_neg, cpow_neg]

theorem not_isNormPowChar_invChar (χ : HeckeChar F) (h : ¬ IsNormPowChar F χ) :
    ¬ IsNormPowChar F (invChar χ) := by
  rintro ⟨τ₀, hτ₀⟩
  refine h ⟨-τ₀, ?_⟩
  rw [← inv_invChar χ, hτ₀, inv_normPowChar]

/-- **The branch of characters which are not norm powers.**  If the finite Hecke functions of
all unitary Hecke characters of `F` have no zero in `Re s > 1/2` (away from the pole of the
norm powers), then the completed function of a character which is not a norm power has no zero
off the critical line. -/
theorem ne_branch (F : Type) [Field F] [NumberField F]
    (hgrh : ∀ (χ : HeckeChar F) (s : ℂ), (1 / 2 : ℝ) < s.re →
      ¬ (∃ τ₀ : ℝ, χ.toFun = normPowChar F τ₀ ∧ s = 1 - (τ₀ : ℂ) * I) → heckeLFin F χ s ≠ 0)
    (χ : HeckeChar F) (h : ¬ IsNormPowChar F χ) (s : ℂ) (hs : s.re ≠ 1 / 2) :
    heckeLCompleted F χ s ≠ 0 := by
  have hΛdef : heckeLCompleted F χ = heckeLCompletedNe F χ h := by
    unfold heckeLCompleted
    rw [dif_neg h]
  have hLdef : heckeLFin F χ = heckeLFinNe F χ h := by
    unfold heckeLFin
    rw [dif_neg h]
  obtain ⟨hLd, hLeq⟩ := heckeLFinNe_spec F χ h
  obtain ⟨hΛd, hΛeq⟩ := heckeLCompletedNe_spec F χ h
  rw [hΛdef]
  rcases lt_or_gt_of_ne hs with hlt | hgt
  · -- `Re s < 1/2`: reflect to `1 - s` with the functional equation.
    have hi : ¬ IsNormPowChar F (invChar χ) := not_isNormPowChar_invChar χ h
    have hLidef : heckeLFin F (invChar χ) = heckeLFinNe F (invChar χ) hi := by
      unfold heckeLFin
      rw [dif_neg hi]
    obtain ⟨hLid, hLieq⟩ := heckeLFinNe_spec F (invChar χ) hi
    -- the archimedean parameters of `χ⁻¹` are the opposites of those of `χ`
    have hτ' : ∀ (v : InfinitePlace F) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar (invChar χ).toFun v x : ℂˣ) : ℂ) =
          (((ideleNorm F (archUnitHom v x)) : ℝ) : ℂ) ^ (((-archτ F χ v : ℝ) : ℂ) * I) := by
      intro v x h1 h2
      have h3 := archτ_spec F χ v x h1 h2
      rw [archLocalChar_invChar, Units.val_inv_eq_inv_val, h3, ofReal_neg, neg_mul, cpow_neg]
    have hm' : ∀ (v : InfinitePlace F) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar (invChar χ).toFun v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (-archm F χ v) := by
      intro v x h1
      have h3 := archm_spec F χ v x h1
      rw [archLocalChar_invChar, Units.val_inv_eq_inv_val, h3, zpow_neg]
    -- the completed function of `χ⁻¹` built with these parameters
    obtain ⟨L₂, Λ₂, hL₂d, hΛ₂d, hL₂eq, hΛ₂eq⟩ :=
      exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq_of_ne_normPowChar
        F (invChar χ).toFun (invChar χ).cont (invChar χ).unitary (invChar χ).classChar
        (fun v => -archτ F χ v) (fun v => -archm F χ v) hτ' hm' (fun τ₀ hτ₀ => hi ⟨τ₀, hτ₀⟩)
    have hLi_eq : L₂ = heckeLFinNe F (invChar χ) hi :=
      entire_eq_of_eq_on_re_gt_one hL₂d hLid fun w hw => (hL₂eq w hw).trans (hLieq w hw).symm
    subst hLi_eq
    -- its Euler product, written with the inverse Satake parameters of `χ`
    have hP' : ∀ w : ℂ, 1 < w.re → heckeLFinNe F (invChar χ) hi w =
        ∏' v : HeightOneSpectrum (𝓞 F),
          (1 - (if IsUnramifiedCharAt χ.toFun v then
            (((χ.toFun (uniformizerIdele F v))⁻¹ : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹ := by
      intro w hw
      rw [hLieq w hw]
      unfold heckeEulerProduct
      refine tprod_congr fun v => ?_
      by_cases hv : IsUnramifiedCharAt χ.toFun v
      · rw [if_pos hv, if_pos ((isUnramified_invChar χ v).mpr hv), invChar_apply]
      · rw [if_neg hv, if_neg fun h' => hv ((isUnramified_invChar χ v).mp h')]
    -- its archimedean factor, written with the parameters of `χ`
    have hγ' : ∀ z : ℂ, 0 < z.re → Λ₂ z =
        (∏ v : InfinitePlace F,
          (if v.IsReal then
            Gammaℝ (z - ((archτ F χ v : ℝ) : ℂ) * I + (((archm F χ v).natAbs % 2 : ℕ) : ℂ))
          else
            Gammaℂ (z - ((archτ F χ v : ℝ) : ℂ) * I + (((archm F χ v).natAbs : ℕ) : ℂ) / 2))) *
          heckeLFinNe F (invChar χ) hi z := by
      intro z hz
      rw [hΛ₂eq z hz]
      congr 1
      refine Finset.prod_congr rfl fun v _ => ?_
      simp only [Int.natAbs_neg, ofReal_neg, neg_mul, sub_eq_add_neg]
    -- finiteness of ramification and the functional equation
    obtain ⟨S, hS⟩ :=
      exists_finset_forall_isUnramifiedCharAt_of_continuous F χ.toFun (continuous_toFun χ)
    obtain ⟨Nf, hNf, hFE⟩ :=
      exists_forall_prod_Gamma_mul_eulerProduct_one_sub_eq_mul_cpow_mul_of_archLocalChar_eq F S
        (fun v => localChar χ.toFun v)
    obtain ⟨hA, -⟩ := hFE χ.toFun χ.cont χ.unitary χ.classChar hS (fun v _ u _ _ => rfl)
      (archτ F χ) (archm F χ) (archτ_spec F χ) (archm_spec F χ)
    obtain ⟨ε, hε, hfe⟩ := hA (fun τ₀ hτ₀ => h ⟨τ₀, hτ₀⟩) (heckeLFinNe F χ h) hLd hLeq
      (heckeLFinNe F (invChar χ) hi) hLid hP' (heckeLCompletedNe F χ h) Λ₂ hΛd hΛ₂d hΛeq hγ'
    intro h0
    have h1 : Λ₂ (1 - s) = 0 := by rw [hfe s, h0, mul_zero]
    have hre : (1 / 2 : ℝ) < (1 - s).re := by
      simp only [sub_re, one_re]
      linarith
    have hre0 : 0 < (1 - s).re := by linarith
    rw [hΛ₂eq (1 - s) hre0] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact gammaProd_ne_zero (fun v => -archτ F χ v) (fun v => -archm F χ v) (1 - s) hre0 h2
    · rw [← hLidef] at h2
      exact hgrh (invChar χ) (1 - s) hre (fun ⟨τ₀, hτ₀, _⟩ => hi ⟨τ₀, hτ₀⟩) h2
  · -- `Re s > 1/2`: the Gamma factor is a unit and the finite function does not vanish.
    have hre0 : 0 < s.re := by linarith
    rw [hΛeq s hre0]
    refine mul_ne_zero (gammaProd_ne_zero (archτ F χ) (archm F χ) s hre0) ?_
    rw [← hLdef]
    exact hgrh χ s hgt (fun ⟨τ₀, hτ₀, _⟩ => h ⟨τ₀, hτ₀⟩)

end MusicOfPrimes.CL

end

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal Complex
open scoped Classical BigOperators

namespace MusicOfPrimes.CL

/-- The converse implication, recorded for completeness: a zero of a finite Hecke function in
`Re s > 1/2` is a zero of the completed function, so the critical-line form implies the
half-plane form.  Together with `solution` this shows that the two statements are equivalent. -/
theorem grh_of_critical_line (F : Type) [Field F] [NumberField F]
    (hcl : ∀ (χ : HeckeChar F) (s : ℂ), s.re ≠ 1 / 2 →
      ¬ (∃ τ₀ : ℝ, χ.toFun = normPowChar F τ₀ ∧
        (s = -(τ₀ : ℂ) * I ∨ s = 1 - (τ₀ : ℂ) * I)) →
      heckeLCompleted F χ s ≠ 0)
    (χ : HeckeChar F) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hpole : ¬ (∃ τ₀ : ℝ, χ.toFun = normPowChar F τ₀ ∧ s = 1 - (τ₀ : ℂ) * I)) :
    heckeLFin F χ s ≠ 0 := by
  have hpole' : ¬ (∃ τ₀ : ℝ, χ.toFun = normPowChar F τ₀ ∧
      (s = -(τ₀ : ℂ) * I ∨ s = 1 - (τ₀ : ℂ) * I)) := by
    rintro ⟨τ₀, h1, h2 | h2⟩
    · have h3 : s.re = 0 := by
        rw [h2]
        simp
      linarith
    · exact hpole ⟨τ₀, h1, h2⟩
  have hΛ := hcl χ s (ne_of_gt hs) hpole'
  intro h0
  apply hΛ
  by_cases h : IsNormPowChar F χ
  · have hLfin : heckeLFin F χ s = dedekindZetaCont F (s + (normPowτ F χ h : ℂ) * I) := by
      unfold heckeLFin
      rw [dif_pos h]
    have hLc : heckeLCompleted F χ s =
        ((((|NumberField.discr F| : ℤ) : ℂ)) ^ ((s + (normPowτ F χ h : ℂ) * I) / 2))⁻¹ *
          dedekindCompleted F (s + (normPowτ F χ h : ℂ) * I) := by
      unfold heckeLCompleted
      rw [dif_pos h]
    have hzre : (s + (normPowτ F χ h : ℂ) * I).re = s.re := by simp
    have hz1 : s + (normPowτ F χ h : ℂ) * I ≠ 1 := fun e =>
      hpole ⟨normPowτ F χ h, normPowτ_spec F χ h, by linear_combination e⟩
    rw [hLc, dedekindCompleted_eq F (by rw [hzre]; exact hs) hz1, ← hLfin, h0, mul_zero,
      mul_zero]
  · have hΛdef : heckeLCompleted F χ = heckeLCompletedNe F χ h := by
      unfold heckeLCompleted
      rw [dif_neg h]
    have hLdef : heckeLFin F χ = heckeLFinNe F χ h := by
      unfold heckeLFin
      rw [dif_neg h]
    rw [hΛdef, (heckeLCompletedNe_spec F χ h).2 s (by linarith), ← hLdef, h0, mul_zero]

end MusicOfPrimes.CL

open MusicOfPrimes in
/-- **Introduction §1.8.5.1, critical-line form.**  Assuming the zero-free half-plane
`MusicOfPrimes.hecke_grh`, the completed Hecke L-function of a unitary Hecke character has no
zero off the line `Re s = 1/2`. -/
theorem solution (F : Type) [Field F] [NumberField F] (χ : HeckeChar F) {s : ℂ}
    (hs : s.re ≠ 1 / 2)
    (hpole : ¬ (∃ τ₀ : ℝ, χ.toFun = normPowChar F τ₀ ∧ (s = -(τ₀ : ℂ) * I ∨ s = 1 - (τ₀ : ℂ) * I))) :
    heckeLCompleted F χ s ≠ 0 := by
  have hgrh : ∀ (χ : HeckeChar F) (s : ℂ), (1 / 2 : ℝ) < s.re →
      ¬ (∃ τ₀ : ℝ, χ.toFun = normPowChar F τ₀ ∧ s = 1 - (τ₀ : ℂ) * I) →
      heckeLFin F χ s ≠ 0 :=
    fun χ s hs hp => hecke_grh F χ hs hp
  by_cases h : IsNormPowChar F χ
  · exact CL.pow_branch F hgrh χ h s hs hpole
  · exact CL.ne_branch F hgrh χ h s hs
