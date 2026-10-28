-- Prove2me | solution 1 for OAI.LargePrimeGaps.unorderedWeight_detector_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T04:58:42.424988+00:00
-- url     : https://prove2.me/submissions/8ba2b2d0-1e72-4238-a7bc-e000f0353f0b

import Mathlib
import Definitions.Def_OAIW2PG000
import Theorems.Thm_OAI_LargePrimeGaps_extra_cumulative_pair_limit
import Theorems.Thm_OAI_LargePrimeGaps_unorderedWeight_external_marked_limit

section
-- module Solutions.OAIW2_P344.Compat
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_Indices
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

theorem log_pos_of_two_le {X : ℕ} (hX : 2 ≤ X) : 0 < Real.log (X : ℝ) :=
  Real.log_pos (by exact_mod_cast (show 1 < X by omega))

theorem theta_nonneg (n : ℕ) : 0 ≤ theta n := by
  by_cases hn : Nat.Prime n
  · simp only [theta, ite_eq_left hn]
    exact (log_pos_of_two_le hn.two_le).le
  · simp [theta, hn]

open Filter

theorem blockLength_le_mul_log {lam : ℝ} (hlam : 0 ≤ lam) {X : ℕ} (hX : 2 ≤ X) :
    (blockLength lam X : ℝ) ≤ lam * Real.log (X : ℝ) :=
  Nat.floor_le (mul_nonneg hlam (log_pos_of_two_le hX).le)

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_DivisorSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

theorem logCoordinates_nonneg {ι : Type*} {X : ℕ} (hX : 2 ≤ X)
    {d : ι → ℕ} (hd : ∀ i, 0 < d i) (i : ι) : 0 ≤ logCoordinates X d i := by
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hd i)) (log_pos_of_two_le hX).le

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_ZetaKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

theorem mem_nonemptySubsets {ι : Type*} {s S : Finset ι} :
    S∈nonemptySubsets s ↔ S.Nonempty ∧ S⊆s := by
  classical
  simp [nonemptySubsets, Finset.nonempty_iff_ne_empty]

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_EulerProducts
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

theorem mem_fiberSubsetFamily {ι α : Type*} [Fintype ι] (b : ι → α)
    (R : Finset α) (S : Finset ι) :
    S∈fiberSubsetFamily b R ↔ S.Nonempty ∧ ∃ r∈R, ∀ i∈S, b i=r := by
  classical
  simp only [fiberSubsetFamily, Finset.mem_biUnion, mem_nonemptySubsets]
  constructor
  · rintro ⟨r,hr,hS,hsub⟩
    exact ⟨hS,r,hr,fun i hi => (Finset.mem_filter.mp (hsub hi)).2⟩
  · rintro ⟨hS,r,hr,hsub⟩
    exact ⟨r,hr,hS,fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsub i hi⟩⟩

theorem disjoint_nonemptySubsets_fibers {ι α : Type*} [Fintype ι] (b : ι → α)
    {r s : α} (hrs : r≠s) :
    Disjoint (nonemptySubsets (Finset.univ.filter fun i => b i=r))
      (nonemptySubsets (Finset.univ.filter fun i => b i=s)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro S hSr hSs
  rcases mem_nonemptySubsets.mp hSr with ⟨hS,hR⟩
  have hT := (mem_nonemptySubsets.mp hSs).2
  rcases hS with ⟨i,hi⟩
  exact hrs ((Finset.mem_filter.mp (hR hi)).2.symm.trans (Finset.mem_filter.mp (hT hi)).2)

theorem mem_fiberSubsetFamily_image {ι α : Type*} [Fintype ι] [DecidableEq α] (b : ι → α)
    (S : Finset ι) :
    S∈fiberSubsetFamily b (Finset.univ.image b) ↔
      S.Nonempty ∧ ∀ i∈S, ∀ j∈S, b i=b j := by
  classical
  rw [mem_fiberSubsetFamily]
  constructor
  · rintro ⟨hS,r,_,hb⟩
    exact ⟨hS,fun i hi j hj => (hb i hi).trans (hb j hj).symm⟩
  · rintro ⟨hS,hb⟩
    rcases hS with ⟨i,hi⟩
    exact ⟨⟨i,hi⟩,b i,Finset.mem_image_of_mem _ (Finset.mem_univ _),fun j hj => hb j hj i hi⟩

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_FourierNormalization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

section FourierNormalization

open scoped FourierTransform SchwartzMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem radianFourier_inversion (G : SchwartzMap V ℂ) (v : V) :
    (∫ u : V, radianFourier G u * Complex.exp (-Complex.I*(inner ℝ u v : ℂ))) = G v := by
  let A : ℝ := 2*Real.pi
  have hA : 0<A := by dsimp [A]; positivity
  let f := fun u : V => (𝓕⁻ G) u * Complex.exp (-Complex.I*((A*inner ℝ u v : ℝ):ℂ))
  have hscale : (∫ u : V, f (A⁻¹ • u)) = A^Module.finrank ℝ V • ∫ u : V, f u := by
    simpa only [inv_pow, inv_inv] using Measure.integral_comp_smul_of_nonneg volume f A⁻¹ (hR:= (inv_pos.mpr hA).le)
  have hinv : (∫ u : V, f u) = G v := by
    have hh := congrArg (fun H : SchwartzMap V ℂ => H v) (FourierTransform.fourier_fourierInv_eq (F := SchwartzMap V ℂ) G)
    rw [SchwartzMap.fourier_coe, Real.fourier_eq'] at hh
    convert hh using 1
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp only [f, A]
    rw [smul_eq_mul, mul_comm]
    congr 2
    push_cast
    ring_nf
  calc
    _ = ∫ u : V, (A^Module.finrank ℝ V)⁻¹ • f (A⁻¹ • u) := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [radianFourier, smul_apply,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
        frequencyDilation_apply]
      dsimp only [f, A]
      rw [real_inner_smul_left]
      have ht : 2*Real.pi*((2*Real.pi)⁻¹*inner ℝ u v) = inner ℝ u v := by field_simp
      rw [ht]
      simp only [Complex.real_smul, mul_assoc]
    _ = (A^Module.finrank ℝ V)⁻¹ • ∫ u : V, f (A⁻¹ • u) := integral_smul _ _
    _ = (A^Module.finrank ℝ V)⁻¹ • (A^Module.finrank ℝ V • G v) := by rw [hscale, hinv]
    _ = G v := by rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hA.ne'), one_smul]

theorem sourceFourier_inversion (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : V) :
    (∫ u : V, sourceFourier ℓ F hF hFs u *
      Complex.exp (-(ℓ v : ℂ)-Complex.I*(inner ℝ u v : ℂ))) = F v := by
  calc
    _ = Complex.exp (-(ℓ v : ℂ)) *
        ∫ u : V, sourceFourier ℓ F hF hFs u *
          Complex.exp (-Complex.I*(inner ℝ u v : ℂ)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      rw [sub_eq_add_neg, Complex.exp_add]
      ring_nf
    _ = Complex.exp (-(ℓ v : ℂ)) * (Complex.exp (ℓ v : ℂ)*F v) := by
      rw [sourceFourier, radianFourier_inversion, laplaceSchwartz_apply]
    _ = F v := by rw [← mul_assoc, ← Complex.exp_add]; simp

end FourierNormalization

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_ContourSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

theorem nonemptySubsets_singleton {ι : Type*} (i : ι) :
    nonemptySubsets {i} = {{i}} := by
  classical
  ext S
  simp [nonemptySubsets,Finset.subset_singleton_iff]
  aesop

theorem nonemptySubsets_pair {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i≠j) :
    nonemptySubsets {i,j} = {{i},{j},{i,j}} := by
  classical
  ext S
  simp only [nonemptySubsets, Finset.mem_erase, Finset.mem_powerset,
    Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨hne,he⟩
    have h : S=∅ ∨ S={i} ∨ S={j} ∨ S={i,j} := by
      have hp := Finset.mem_powerset.mpr he
      simp [Finset.powerset_insert] at hp
      aesop
    exact h.resolve_left (hne)
  · rintro (rfl|rfl|rfl) <;> simp

theorem fiberKernel_singleton {ι : Type*} (i : ι) (w : ι → ℂ) :
    fiberKernel {i} w = w i := by
  simp [fiberKernel,nonemptySubsets_singleton]

theorem fiberKernel_pair {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i≠j) (w : ι → ℂ) :
    fiberKernel {i,j} w = w i*w j/(w i+w j) := by
  rw [fiberKernel,nonemptySubsets_pair hij]
  have h1 : ({j} : Finset ι)≠{i,j} := by simp [Finset.ext_iff,hij]
  have h2 : ({i} : Finset ι)≠{j} := by simp [hij]
  have h3 : ({i} : Finset ι)≠{i,j} := by simp [Finset.ext_iff,hij.symm]
  simp [h1,h2,h3,hij,div_eq_mul_inv]
  ring

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_FourierDerivatives
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

section FourierDerivative

open scoped FourierTransform SchwartzMap ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

open LineDeriv

theorem radianFourier_lineDeriv (G : SchwartzMap V ℂ) (m u : V) :
    radianFourier (∂_{m} G) u = -Complex.I*(inner ℝ u m:ℂ)*radianFourier G u := by
  have hg : (inner ℝ · m).HasTemperateGrowth := by fun_prop
  simp only [radianFourier,SchwartzMap.fourierInv_lineDerivOp_eq,
    smul_apply,SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    frequencyDilation_apply,SchwartzMap.smulLeftCLM_apply hg,real_inner_smul_left,
    smul_eq_mul,Complex.real_smul]
  push_cast
  field_simp

theorem radianFourier_add (G H : SchwartzMap V ℂ) (u : V) :
    radianFourier (G+H) u = radianFourier G u+radianFourier H u := by
  simp only [radianFourier, FourierTransform.fourierInv_add, map_add, smul_add, add_apply]

theorem radianFourier_const_mul (c : ℂ) (G : SchwartzMap V ℂ) (u : V) :
    radianFourier (c • G) u = c*radianFourier G u := by
  simp only [radianFourier, FourierTransform.fourierInv_smul, map_smul, smul_apply,Complex.real_smul,smul_eq_mul]
  ring

theorem radianFourier_laplaceLineDeriv (ℓ : V →L[ℝ] ℝ) (m : V)
    (G : SchwartzMap V ℂ) (u : V) :
    radianFourier (laplaceLineDeriv ℓ m G) u =
      ((ℓ m : ℂ)+Complex.I*(inner ℝ u m:ℂ))*radianFourier G u := by
  rw [laplaceLineDeriv, radianFourier_add, radianFourier_const_mul,
    radianFourier_const_mul, radianFourier_lineDeriv]
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem laplaceLineDeriv_apply (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (m v : V) :
    laplaceLineDeriv ℓ m (laplaceSchwartz ℓ F hF hFs) v =
      Complex.exp (ℓ v : ℂ)*(-fderiv ℝ F v m) := by
  have hlin := Complex.ofRealCLM.hasFDerivAt.comp v ℓ.hasFDerivAt
  have he := hlin.cexp
  have hf := he.mul ((hFs.differentiable (by simp)).differentiableAt.hasFDerivAt (x := v))
  simp only [laplaceLineDeriv, add_apply, smul_apply, smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, laplaceSchwartz_apply]
  change (ℓ m:ℂ)*(Complex.exp (ℓ v:ℂ)*F v) +
    -1*(fderiv ℝ (fun v => Complex.exp (ℓ v:ℂ)*F v) v m) = _
  have hd := congrArg (fun A : V →L[ℝ] ℂ => A m) hf.fderiv
  simp only [Function.comp_apply, add_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul] at hd
  change (fderiv ℝ (fun x => Complex.exp (ℓ x:ℂ)*F x) v) m =
    Complex.exp (ℓ v:ℂ)*fderiv ℝ F v m + F v*(Complex.exp (ℓ v:ℂ)*(ℓ m:ℂ)) at hd
  rw [hd]
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem laplaceLineDeriv_laplaceSchwartz (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (m : V) :
    laplaceLineDeriv ℓ m (laplaceSchwartz ℓ F hF hFs) =
      laplaceSchwartz ℓ (fun v => -fderiv ℝ F v m) (hF.fderiv_apply ℝ m |>.neg)
        (contDiff_signedLineDeriv F hFs m) := by
  ext v
  exact laplaceLineDeriv_apply ℓ F hF hFs m v

theorem sourceFourier_signedLineDeriv (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (m u : V) :
    sourceFourier ℓ (fun v => -fderiv ℝ F v m) (hF.fderiv_apply ℝ m |>.neg)
        (contDiff_signedLineDeriv F hFs m) u =
      ((ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ))*sourceFourier ℓ F hF hFs u := by
  unfold sourceFourier
  rw [← laplaceLineDeriv_laplaceSchwartz, radianFourier_laplaceLineDeriv]

theorem sourceFourier_signedDirections (ℓ : V →L[ℝ] ℝ) (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (u : V) :
    sourceFourier ℓ (signedDirections ms F) (signedDirections_compact ms F hF)
        (signedDirections_smooth ms F hFs) u =
      (ms.map (fun m => ((ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ)))).prod *
        sourceFourier ℓ F hF hFs u := by
  induction ms with
  | nil => simp [signedDirections]
  | cons m ms ih =>
    change sourceFourier ℓ (fun v => -fderiv ℝ (signedDirections ms F) v m) _ _ u = _
    rw [sourceFourier_signedLineDeriv ℓ (signedDirections ms F)
      (signedDirections_compact ms F hF) (signedDirections_smooth ms F hFs),ih]
    simp only [List.map_cons,List.prod_cons,mul_assoc]

theorem sourceFourier_derivative_inversion (ℓ : V →L[ℝ] ℝ) (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : V) :
    (∫ u : V, sourceFourier ℓ F hF hFs u *
      (ms.map (fun m => ((ℓ m:ℂ)+Complex.I*(inner ℝ u m:ℂ)))).prod *
      Complex.exp (-(ℓ v:ℂ)-Complex.I*(inner ℝ u v:ℂ))) = signedDirections ms F v := by
  rw [← sourceFourier_inversion ℓ (signedDirections ms F)
    (signedDirections_compact ms F hF) (signedDirections_smooth ms F hFs) v]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [sourceFourier_signedDirections,mul_comm (sourceFourier ℓ F hF hFs u)]

end FourierDerivative

theorem familyKernel_fibers {ι α : Type*} [Fintype ι] (b : ι → α)
    (R : Finset α) (w : ι → ℂ) :
    familyKernel (fiberSubsetFamily b R) w =
      ∏ r∈R, fiberKernel (Finset.univ.filter fun i => b i=r) w := by
  classical
  unfold familyKernel fiberSubsetFamily fiberKernel
  rw [Finset.prod_biUnion]
  intro r _ s _ hrs
  exact disjoint_nonemptySubsets_fibers b hrs

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_LaplaceTransform
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

section FourierLaplace

open scoped FourierTransform SchwartzMap ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem positiveOrthantMeasure_eq_restrict (α : Type*) [Fintype α] :
    positiveOrthantMeasure α = volume.restrict (Set.pi univ (fun _ : α => Ioi (0:ℝ))) := by
  rw [volume_pi,Measure.restrict_pi_pi]
  rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem product_laplace_exp_eq {α : Type*} [Fintype α] (ℓ : V →L[ℝ] ℝ)
    (m : α → V) (u : V) (y : α → ℝ) :
    (∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ))) =
      Complex.exp (-(ℓ (rayVector m y):ℂ)-Complex.I*(inner ℝ u (rayVector m y):ℂ)) := by
  rw [← Complex.exp_sum]
  congr 1
  simp only [rayVector,map_sum,map_smul,smul_eq_mul,inner_sum,inner_smul_right,
    Complex.ofReal_sum,Complex.ofReal_mul]
  rw [← Finset.sum_neg_distrib,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold laplaceFrequency
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem norm_product_laplace_exp {α : Type*} [Fintype α] (ℓ : V →L[ℝ] ℝ)
    (m : α → V) (u : V) (y : α → ℝ) :
    ‖∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ))‖ =
      ∏ i, Real.exp (-ℓ (m i) * y i) := by
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp [Complex.norm_exp,laplaceFrequency]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem integral_product_laplace_exp {α : Type*} [Fintype α]
    (ℓ : V →L[ℝ] ℝ) (m : α → V) (hm : ∀ i, 0<ℓ (m i)) (u : V) :
    (∫ y, ∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ))
      ∂positiveOrthantMeasure α) = ∏ i, (laplaceFrequency ℓ (m i) u)⁻¹ := by
  rw [positiveOrthantMeasure,integral_fintype_prod_eq_prod
    (fun i (y : ℝ) => Complex.exp (-laplaceFrequency ℓ (m i) u * (y:ℂ)))]
  apply Finset.prod_congr rfl
  intro i _
  simpa using integral_exp_mul_complex_Ioi (a:=-laplaceFrequency ℓ (m i) u)
    (by simp [hm i]) 0

theorem schwartz_product_laplace_integrable {α : Type*} [Fintype α]
    (Ψ : SchwartzMap V ℂ) (ℓ : V →L[ℝ] ℝ) (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    Integrable (fun z : V × (α → ℝ) => Ψ z.1 *
      ∏ i, Complex.exp (-laplaceFrequency ℓ (m i) z.1 * (z.2 i:ℂ)))
      (volume.prod (positiveOrthantMeasure α)) := by
  have he : Integrable (fun y : α → ℝ => ∏ i, Real.exp (-ℓ (m i)*y i))
      (positiveOrthantMeasure α) := by
    exact Integrable.fintype_prod (f := fun i y => Real.exp (-ℓ (m i)*y))
      (μ := fun _ => volume.restrict (Ioi 0))
      (fun i => integrableOn_exp_mul_Ioi (by linarith [hm i]) 0)
  have hb := (Ψ.integrable (μ := volume)).norm.mul_prod he
  apply hb.mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul (Ψ.continuous.comp continuous_fst)
    apply continuous_finsetProd
    intro i _
    unfold laplaceFrequency
    fun_prop
  · filter_upwards [] with z
    rw [norm_mul,norm_product_laplace_exp]

theorem schwartz_product_laplace_interchange {α : Type*} [Fintype α]
    (Ψ : SchwartzMap V ℂ) (ℓ : V →L[ℝ] ℝ) (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    (∫ u : V, Ψ u*(∏ i, (laplaceFrequency ℓ (m i) u)⁻¹)) =
      ∫ y, (∫ u : V, Ψ u *
        Complex.exp (-(ℓ (rayVector m y):ℂ)-Complex.I*(inner ℝ u (rayVector m y):ℂ)))
        ∂positiveOrthantMeasure α := by
  calc
    _ = ∫ u : V, ∫ y, Ψ u*(∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ)))
        ∂positiveOrthantMeasure α := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [integral_const_mul,integral_product_laplace_exp ℓ m hm]
    _ = ∫ y, (∫ u : V, Ψ u*(∏ i, Complex.exp (-laplaceFrequency ℓ (m i) u * (y i:ℂ))))
        ∂positiveOrthantMeasure α :=
      integral_integral_swap (schwartz_product_laplace_integrable Ψ ℓ m hm)
    _ = _ := by simp only [product_laplace_exp_eq]

theorem sourceFourier_product_laplace {α : Type*} [Fintype α]
    (ℓ : V →L[ℝ] ℝ) (F : V → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    (∫ u : V, sourceFourier ℓ F hF hFs u*(∏ i, (laplaceFrequency ℓ (m i) u)⁻¹)) =
      ∫ y, F (rayVector m y) ∂positiveOrthantMeasure α := by
  rw [schwartz_product_laplace_interchange _ ℓ m hm]
  simp only [sourceFourier_inversion]

theorem sourceFourier_derivative_laplace {α : Type*} [Fintype α]
    (ℓ : V →L[ℝ] ℝ) (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (m : α → V) (hm : ∀ i, 0<ℓ (m i)) :
    (∫ u : V, sourceFourier ℓ F hF hFs u *
      (ms.map (fun m => laplaceFrequency ℓ m u)).prod *
      (∏ i, (laplaceFrequency ℓ (m i) u)⁻¹)) =
      ∫ y, signedDirections ms F (rayVector m y) ∂positiveOrthantMeasure α := by
  rw [← sourceFourier_product_laplace ℓ (signedDirections ms F)
    (signedDirections_compact ms F hF) (signedDirections_smooth ms F hFs) m hm]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [sourceFourier_signedDirections ℓ ms F hF hFs u]
  simp only [laplaceFrequency,mul_comm (sourceFourier ℓ F hF hFs u)]

end FourierLaplace

theorem fiberKernel_card_le_two {ι : Type*} (S : Finset ι) (hS : S.card≤2) (w : ι → ℂ) :
    fiberKernel S w = (∏ i∈S, w i)*if S.card=2 then (∑ i∈S, w i)⁻¹ else 1 := by
  classical
  have hc : S.card=0 ∨ S.card=1 ∨ S.card=2 := by omega
  rcases hc with hc|hc|hc
  · have hs : S=∅ := Finset.card_eq_zero.mp hc
    subst S
    simp [fiberKernel,nonemptySubsets]
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hc
    simp [fiberKernel_singleton]
  · obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hc
    simp [fiberKernel_pair hij,hij,div_eq_mul_inv]

theorem familyKernel_small_fibers {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (hR : ∀ i, b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2) (w : ι → ℂ) :
    familyKernel (fiberSubsetFamily b R) w =
      (∏ i, w i)*(∏ r∈R.filter (fun r => (Finset.univ.filter fun i => b i=r).card=2),
        (∑ i∈Finset.univ.filter (fun i => b i=r), w i)⁻¹) := by
  classical
  rw [familyKernel_fibers]
  calc
    _ = ∏ r∈R, (∏ i∈Finset.univ.filter (fun i => b i=r), w i)*
        (if (Finset.univ.filter (fun i => b i=r)).card=2 then
          (∑ i∈Finset.univ.filter (fun i => b i=r), w i)⁻¹ else 1) := by
      apply Finset.prod_congr rfl
      intro r hr
      exact fiberKernel_card_le_two _ (hcard r hr) w
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_fiberwise_of_maps_to (fun i _ => hR i)]
      congr 1
      exact (Finset.prod_filter ..).symm

section SmallFiberCoefficient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem laplaceFrequency_sum {α : Type*} (ℓ : V →L[ℝ] ℝ) (S : Finset α)
    (m : α → V) (u : V) :
    laplaceFrequency ℓ (∑ i∈S, m i) u = ∑ i∈S, laplaceFrequency ℓ (m i) u := by
  simp [laplaceFrequency,map_sum,inner_sum,Complex.ofReal_sum,Finset.mul_sum,Finset.sum_add_distrib]

@[simp] theorem laplaceFrequency_fiberRay {ι α : Type*} [Fintype ι]
    (b : ι → α) (r : α) (u : EuclideanSpace ℝ ι) :
    laplaceFrequency (fourierCoordinateSum ι) (fiberRay b r) u =
      ∑ i∈Finset.univ.filter (fun i => b i=r), frequencyW (u i) := by
  classical
  simp [fiberRay,laplaceFrequency_sum]

theorem fiberRay_positive {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (r : doubleFibers b R) :
    0 < fourierCoordinateSum ι (fiberRay b r.val) := by
  classical
  have hr : (Finset.univ.filter (fun i => b i=r.val)).card=2 :=
    (Finset.mem_filter.mp r.property).2
  have h := congrArg Complex.re (laplaceFrequency_fiberRay b r.val (0 : EuclideanSpace ℝ ι))
  simp only [laplaceFrequency_re,Complex.re_sum,frequencyW_re,Finset.sum_const] at h
  rw [h,hr]
  norm_num

theorem small_fiber_kernelConstant {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (hR : ∀ i, b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2)
    (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    kernelConstant (sourceFourier (fourierCoordinateSum ι) F hF hFs) (fiberSubsetFamily b R) =
      ∫ y, signedDirections (coordinateDirectionList ι) F
        (rayVector (fun r : doubleFibers b R => fiberRay b r.val) y)
          ∂positiveOrthantMeasure (doubleFibers b R) := by
  classical
  rw [← sourceFourier_derivative_laplace (fourierCoordinateSum ι) (coordinateDirectionList ι)
    F hF hFs (fun r : doubleFibers b R => fiberRay b r.val) (fiberRay_positive b R)]
  unfold kernelConstant
  apply integral_congr_ae
  filter_upwards [] with u
  rw [contourKernel,familyKernel_small_fibers b R hR hcard,coordinateDirectionList_multiplier]
  simp only [laplaceFrequency_fiberRay]
  have hp := Finset.prod_coe_sort (s := doubleFibers b R)
    (f := fun r : α => (∑ i∈Finset.univ.filter (fun i => b i=r), frequencyW (u i))⁻¹)
  rw [hp,mul_assoc]
  rfl

end SmallFiberCoefficient

open Topology

open scoped Convolution ContDiff Pointwise

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_CumulativeProfiles
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem cumulativeExtension_tail {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ)
    (hf : ∀ y, f y≠0 → ∀ i, y i≤T)
    (v : EuclideanSpace ℝ ι) (hv : ∀ i, 0≤v i) :
    cumulativeExtension T f v = cumulativeTail f v := by
  have hs : MeasurableSet {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i} := by
    rw [Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_le (continuous_const (y := v i)) (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i)).measurableSet
  unfold cumulativeExtension cumulativeTail
  rw [convolution_def]
  change (∫ t, cubeIndicator T t * f (v-t)) = _
  rw [← integral_sub_left_eq_self (fun t => cubeIndicator T t * f (v-t)) volume v]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [sub_sub_cancel]
  by_cases hfy : f y=0
  · simp [Set.indicator,hfy]
  · by_cases hy : ∀ i, v i≤y i
    · rw [Set.indicator_of_mem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∈negativeCube T := by
        intro i
        change -T≤v i-y i ∧ v i-y i≤0
        constructor <;> linarith [hf y hfy i,hv i,hy i]
      simp [cubeIndicator,Set.indicator_of_mem hcube]
    · rw [Set.indicator_of_notMem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∉negativeCube T := by
        intro h
        apply hy
        intro i
        have := (h i).2
        change v i-y i≤0 at this
        linarith
      simp [cubeIndicator,Set.indicator_of_notMem hcube]

section GeneralDirections

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem signedDirectionalList_smooth (ms : List V) (F : V → ℂ)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (signedDirectionalList ms F) := by
  induction ms with
  | nil => exact hF
  | cons m ms ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const |>.neg

theorem signedDirectionalList_compact (ms : List V) (F : V → ℂ)
    (hF : HasCompactSupport F) : HasCompactSupport (signedDirectionalList ms F) := by
  induction ms with
  | nil => exact hF
  | cons m ms ih => exact (ih.fderiv_apply ℝ m).neg

theorem signedDirectionalList_affine (ms : List V) (F : W → ℂ)
    (hF : ContDiff ℝ ∞ F) (A : V →L[ℝ] W) (c : W) :
    signedDirectionalList ms (fun v => F (c+A v)) =
      fun v => signedDirectionalList (ms.map A) F (c+A v) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    have hd := signedDirectionalList_smooth (ms.map A) F hF
    have hA (v : V) : HasFDerivAt (fun v => c+A v) A v := by
      simpa using (A.hasFDerivAt (x := v)).const_add c
    ext v
    change -fderiv ℝ (signedDirectionalList ms (fun v => F (c+A v))) v m = _
    rw [ih]
    have he := ((hd.differentiable (by simp) (c+A v)).hasFDerivAt.comp v (hA v)).fderiv
    simp only [Function.comp_def] at he
    rw [he]
    rfl

theorem signedDirectionalList_tsupport (ms : List V) (F : V → ℂ) :
    tsupport (signedDirectionalList ms F) ⊆ tsupport F := by
  induction ms with
  | nil => exact Set.Subset.rfl
  | cons m ms ih =>
    change tsupport (fun v => - fderiv ℝ (signedDirectionalList ms F) v m) ⊆ _
    change tsupport (-(fun v => fderiv ℝ (signedDirectionalList ms F) v m)) ⊆ _
    rw [tsupport_neg]
    exact (tsupport_fderiv_apply_subset ℝ m).trans ih

end GeneralDirections

theorem finTailEmbed_single (n : ℕ) (i : Fin n) :
    finTailEmbed n (Pi.single i 1) = Pi.single i.succ 1 := by
  ext j
  cases j using Fin.cases with
  | zero => simp
  | succ j => simp [Pi.single_apply,Fin.succ_inj]

theorem finDirections_succ (n : ℕ) :
    finDirections (n+1) = Pi.single 0 1 :: (finDirections n).map (finTailEmbed n) := by
  simp only [finDirections,List.finRange_succ,List.map_cons,List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (finTailEmbed_single n i).symm

theorem fin_cons_affine {n : ℕ} (a : ℝ) (x : Fin n → ℝ) :
    Fin.cons a x = Pi.single 0 a + finTailEmbed n x := by
  ext i
  cases i using Fin.cases <;> simp

theorem fin_cons_closedEmbedding (n : ℕ) (a : ℝ) :
    IsClosedEmbedding (fun x : Fin n → ℝ => (Fin.cons a x : Fin (n+1) → ℝ)) := by
  have h : Function.Injective (finTailEmbed n) := by
    intro x y hxy
    ext i
    have := congrFun hxy i.succ
    simpa using this
  have he := LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr h)
  have hc := (Homeomorph.addLeft (Pi.single 0 a : Fin (n+1) → ℝ)).isClosedEmbedding.comp he
  convert hc using 1
  funext x
  exact fin_cons_affine a x

theorem fin_cons_head_closedEmbedding (n : ℕ) (y : Fin n → ℝ) :
    IsClosedEmbedding (fun a : ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) := by
  have he : IsClosedEmbedding (fun a : ℝ => a • (Pi.single 0 1 : Fin (n+1) → ℝ)) :=
    isClosedEmbedding_smul_left (by intro h; have := congrFun h 0; simp at this)
  have hc := (Homeomorph.addRight (Fin.cons 0 y : Fin (n+1) → ℝ)).isClosedEmbedding.comp he
  convert hc using 1
  ext a i
  cases i using Fin.cases <;> simp

theorem piTail_integral_cons {n : ℕ} (v : Fin (n+1) → ℝ)
    (f : (Fin (n+1) → ℝ) → ℂ) (hf : Integrable f (piTailMeasure v)) :
    (∫ x, f x ∂piTailMeasure v) =
      ∫ y, (∫ a in Ioi (v 0), f (Fin.cons a y)) ∂piTailMeasure (fun i => v i.succ) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have hm := measurePreserving_piFinSuccAbove
    (fun i : Fin (n+1) => volume.restrict (Ioi (v i))) 0
  have he : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.cons p.1 p.2 := by
    intro p
    simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
  dsimp only [e] at he
  have hprod : Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2))
      ((volume.restrict (Ioi (v 0))).prod (piTailMeasure (fun i => v i.succ))) := by
    have hh := (hm.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hf
    simpa only [Fin.zero_succAbove,he,Function.comp_def,piTailMeasure] using hh
  calc
    _ = ∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2)
        ∂((volume.restrict (Ioi (v 0))).prod (piTailMeasure (fun i => v i.succ))) := by
      have hh := hm.symm.integral_comp' f
      simpa only [Fin.zero_succAbove,he,piTailMeasure] using hh.symm
    _ = _ := integral_prod_symm _ hprod

theorem fin_cons_head_affine {n : ℕ} (a : ℝ) (y : Fin n → ℝ) :
    Fin.cons a y = a • (Pi.single 0 1 : Fin (n+1) → ℝ) + Fin.cons 0 y := by
  ext i
  cases i using Fin.cases <;> simp

theorem fin_cons_hasDerivAt {n : ℕ} (y : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun a => (Fin.cons a y : Fin (n+1) → ℝ)) (Pi.single 0 1) a := by
  have he : (fun a : ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) =
      fun a => a • (Pi.single 0 1 : Fin (n+1) → ℝ) + Fin.cons 0 y :=
    funext (fun a => fin_cons_head_affine a y)
  rw [he]
  simpa using ((hasDerivAt_id a).smul_const (Pi.single 0 1 : Fin (n+1) → ℝ)).add_const
    (Fin.cons 0 y)

theorem fin_cons_head_smooth {n : ℕ} (y : Fin n → ℝ) :
    ContDiff ℝ ∞ (fun a => (Fin.cons a y : Fin (n+1) → ℝ)) := by
  have he : (fun a : ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) =
      fun a => a • (Pi.single 0 1 : Fin (n+1) → ℝ) + Fin.cons 0 y :=
    funext (fun a => fin_cons_head_affine a y)
  rw [he]
  fun_prop

theorem fin_cons_tail_smooth {n : ℕ} (a : ℝ) :
    ContDiff ℝ ∞ (fun y : Fin n → ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) := by
  simp_rw [fin_cons_affine]
  fun_prop

theorem piTail_signedDirections_FTC (n : ℕ) (F : (Fin n → ℝ) → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : Fin n → ℝ) :
    (∫ x, signedDirectionalList (finDirections n) F x ∂piTailMeasure v) = F v := by
  induction n with
  | zero =>
    simp only [finDirections,List.finRange_zero,List.map_nil,signedDirectionalList,List.foldr_nil]
    unfold piTailMeasure
    rw [Measure.pi_of_empty (x := v)]
    exact integral_dirac F v
  | succ n ih =>
    rw [finDirections_succ]
    let ms := (finDirections n).map (finTailEmbed n)
    let H := signedDirectionalList ms F
    have hHc : HasCompactSupport H := signedDirectionalList_compact ms F hF
    have hHs : ContDiff ℝ ∞ H := signedDirectionalList_smooth ms F hFs
    have hfull : Integrable (signedDirectionalList (Pi.single 0 1 :: ms) F) (piTailMeasure v) :=
      (signedDirectionalList_smooth _ F hFs).continuous.integrable_of_hasCompactSupport
        (signedDirectionalList_compact _ F hF)
    rw [piTail_integral_cons v _ hfull]
    have hinner (y : Fin n → ℝ) :
        (∫ a in Ioi (v 0), signedDirectionalList (Pi.single 0 1 :: ms) F (Fin.cons a y)) =
          H (Fin.cons (v 0) y) := by
      have hc : HasCompactSupport (fun a : ℝ => H (Fin.cons a y)) :=
        hHc.comp_isClosedEmbedding (fin_cons_head_closedEmbedding n y)
      have hs : ContDiff ℝ ∞ (fun a : ℝ => H (Fin.cons a y)) :=
        hHs.comp (fin_cons_head_smooth y)
      have hd (a : ℝ) : deriv (fun a : ℝ => H (Fin.cons a y)) a =
          fderiv ℝ H (Fin.cons a y) (Pi.single 0 1) := by
        exact ((hHs.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt a
          (fin_cons_hasDerivAt y a)).deriv
      have he : (fun a : ℝ => signedDirectionalList (Pi.single 0 1 :: ms) F (Fin.cons a y)) =
          fun a => -deriv (fun a : ℝ => H (Fin.cons a y)) a := by
        funext a
        rw [hd]
        rfl
      rw [he,integral_neg,HasCompactSupport.integral_Ioi_deriv_eq (hs.of_le (by simp)) hc,neg_neg]
    simp_rw [hinner]
    let G : (Fin n → ℝ) → ℂ := fun y => F (Fin.cons (v 0) y)
    have hGc : HasCompactSupport G := hF.comp_isClosedEmbedding (fin_cons_closedEmbedding n (v 0))
    have hGs : ContDiff ℝ ∞ G := hFs.comp (fin_cons_tail_smooth (v 0))
    have hg : (fun y : Fin n → ℝ => H (Fin.cons (v 0) y)) = signedDirectionalList (finDirections n) G := by
      have he := signedDirectionalList_affine (finDirections n) F hFs (finTailEmbed n)
        (Pi.single 0 (v 0))
      simpa only [← fin_cons_affine] using he.symm
    rw [hg,ih G hGc hGs (fun i => v i.succ)]
    dsimp only [G]
    congr 1
    ext i
    cases i using Fin.cases <;> rfl

theorem complexCumulativeExtension_compact {ι : Type*} [Fintype ι]
    (T : ℝ) (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F) :
    HasCompactSupport (complexCumulativeExtension T F) :=
  HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (cubeIndicator_compact T) hF

theorem complexCumulativeExtension_smooth {ι : Type*} [Fintype ι]
    (T : ℝ) (F : EuclideanSpace ℝ ι → ℂ) (hF : HasCompactSupport F)
    (hFs : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (complexCumulativeExtension T F) :=
  hF.contDiff_convolution_right _ (cubeIndicator_integrable T).locallyIntegrable hFs

theorem complexCumulativeExtension_tail {ι : Type*} [Fintype ι]
    (T : ℝ) (F : EuclideanSpace ℝ ι → ℂ)
    (hF : ∀ y, F y≠0 → ∀ i, y i≤T)
    (v : EuclideanSpace ℝ ι) (hv : ∀ i, 0≤v i) :
    complexCumulativeExtension T F v = ∫ y in {y | ∀ i, v i≤y i}, F y := by
  have hs : MeasurableSet {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i} := by
    rw [Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_le (continuous_const (y := v i))
      (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i)).measurableSet
  unfold complexCumulativeExtension
  rw [convolution_def]
  change (∫ t, cubeIndicator T t • F (v-t)) = _
  rw [← integral_sub_left_eq_self (fun t => cubeIndicator T t • F (v-t)) volume v]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [sub_sub_cancel]
  by_cases hFy : F y=0
  · simp [Set.indicator,hFy]
  · by_cases hy : ∀ i, v i≤y i
    · rw [Set.indicator_of_mem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∈negativeCube T := by
        intro i
        change -T≤v i-y i ∧ v i-y i≤0
        constructor <;> linarith [hF y hFy i,hv i,hy i]
      simp [cubeIndicator,Set.indicator_of_mem hcube]
    · rw [Set.indicator_of_notMem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∉negativeCube T := by
        intro h
        apply hy
        intro i
        have := (h i).2
        change v i-y i≤0 at this
        linarith
      simp [cubeIndicator,Set.indicator_of_notMem hcube]

theorem signedDirections_cumulative {ι : Type*} [Fintype ι]
    (T : ℝ) (ms : List (EuclideanSpace ℝ ι)) (F : EuclideanSpace ℝ ι → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    signedDirections ms (complexCumulativeExtension T F) =
      complexCumulativeExtension T (signedDirections ms F) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    ext v
    change -fderiv ℝ (signedDirections ms (complexCumulativeExtension T F)) v m = _
    rw [ih]
    have hc := signedDirections_compact ms F hF
    have hs := signedDirections_smooth ms F hFs
    unfold complexCumulativeExtension
    rw [(hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (cubeIndicator_integrable T).locallyIntegrable (hs.of_le (by simp)) v).fderiv]
    rw [convolution_precompR_apply _ (cubeIndicator_integrable T).locallyIntegrable
      (hc.fderiv ℝ) (hs.continuous_fderiv (by simp))]
    simp only [convolution_def,ContinuousLinearMap.lsmul_apply,
      signedDirections,List.foldr_cons,smul_neg,integral_neg]

theorem euclideanTail_signedDirections_FTC (n : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x in {x | ∀ i, v i≤x i}, signedDirections (euclideanFinDirections n) F x) = F v := by
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  have hc : HasCompactSupport (fun x => F (e x)) :=
    hF.comp_isClosedEmbedding e.toHomeomorph.isClosedEmbedding
  have hs : ContDiff ℝ ∞ (fun x => F (e x)) := hFs.comp e.contDiff
  have hFTC := piTail_signedDirections_FTC n (fun x => F (e x)) hc hs v.ofLp
  have ha := signedDirectionalList_affine (finDirections n) F hFs e.toContinuousLinearMap 0
  simp only [zero_add] at ha
  have htail : piTailMeasure v.ofLp = volume.restrict (Ici v.ofLp) := by
    unfold piTailMeasure
    rw [← Measure.restrict_pi_pi]
    exact Measure.restrict_congr_set (Measure.univ_pi_Ioi_ae_eq_Ici (μ := fun _ => volume))
  change signedDirectionalList (finDirections n) (fun x => F (e x)) =
    fun x => signedDirections (euclideanFinDirections n) F (e x) at ha
  rw [htail,ha] at hFTC
  have he := (PiLp.volume_preserving_toLp (Fin n)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
    (signedDirections (euclideanFinDirections n) F) {x | ∀ i, v i≤x i}
  convert he.symm.trans hFTC using 1
  exact congrArg F (by simp [e])

theorem signedDirections_coordinate_eq_fin (n : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    signedDirections (coordinateDirectionList (Fin n)) F =
      signedDirections (euclideanFinDirections n) F := by
  ext v
  rw [← sourceFourier_derivative_inversion (fourierCoordinateSum (Fin n))
    (coordinateDirectionList (Fin n)) F hF hFs v,
    ← sourceFourier_derivative_inversion (fourierCoordinateSum (Fin n))
    (euclideanFinDirections n) F hF hFs v]
  apply integral_congr_ae
  filter_upwards [] with u
  change sourceFourier _ F hF hFs u *
    ((coordinateDirectionList (Fin n)).map (fun m => laplaceFrequency _ m u)).prod * _ =
    sourceFourier _ F hF hFs u *
    ((euclideanFinDirections n).map (fun m => laplaceFrequency _ m u)).prod * _
  rw [coordinateDirectionList_multiplier,euclideanFinDirections_multiplier]

theorem complexCumulativeExtension_signed_full (n : ℕ) (T : ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℂ) (hF : HasCompactSupport F)
    (hFs : ContDiff ℝ ∞ F) (hT : ∀ y∈tsupport F, ∀ i, y i≤T)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ∀ i, 0≤v i) :
    signedDirections (coordinateDirectionList (Fin n)) (complexCumulativeExtension T F) v =
      F v := by
  rw [signedDirections_coordinate_eq_fin n _ (complexCumulativeExtension_compact T F hF)
    (complexCumulativeExtension_smooth T F hF hFs),signedDirections_cumulative T _ F hF hFs]
  rw [complexCumulativeExtension_tail T _ _ v hv]
  · exact euclideanTail_signedDirections_FTC n F hF hFs v
  · intro y hy i
    exact hT y (signedDirectionalList_tsupport (euclideanFinDirections n) F
      (subset_tsupport _ hy)) i

theorem complexCumulativeExtension_ofReal {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ) :
    complexCumulativeExtension T (fun y => (f y:ℂ)) =
      fun v => (cumulativeExtension T f v:ℂ) := by
  ext v
  simp only [complexCumulativeExtension,cumulativeExtension,convolution_def,
    ContinuousLinearMap.lsmul_apply,ContinuousLinearMap.mul_apply',
    Complex.real_smul,← Complex.ofReal_mul,integral_complex_ofReal]

theorem profile_coordinate_upper {n : ℕ} {tau : ℝ} {f : (Fin n → ℝ) → ℝ}
    (hf : tsupport f ⊆ positiveSimplex n tau) (y : Fin n → ℝ) (hy : y∈tsupport f)
    (i : Fin n) : y i≤tau := by
  have hh := hf hy
  exact (Finset.single_le_sum (fun j _ => (hh.1 j).le) (Finset.mem_univ i)).trans hh.2.le

theorem cumulativeProfile_tail {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n tau) (v : Fin n → ℝ) (hv : ∀ i, 0≤v i) :
    cumulativeProfile tau f v = ∫ y in Ici v, f y := by
  unfold cumulativeProfile
  rw [cumulativeExtension_tail tau _ _ _ hv]
  · unfold cumulativeTail
    have hm := (PiLp.volume_preserving_ofLp (Fin n)).setIntegral_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding f (Ici v)
    exact hm
  · intro y hy i
    exact profile_coordinate_upper hf y.ofLp (subset_tsupport f hy) i

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_TensorProfiles
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem cumulativeProfile_budget {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n tau) : HasBudget (cumulativeProfile tau f) tau := by
  intro v hv hsum
  rw [cumulativeProfile_tail tau f hf v hv]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  by_contra hne
  have hh := hf (subset_tsupport f hne)
  have he : tau≤coordinateSum y :=
    hsum.le.trans (Finset.sum_le_sum (fun i _ => hy i))
  exact (not_lt_of_ge he) hh.2

theorem cumulativeProfile_signed_full {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ∀ i, 0≤v i) :
    signedDirections (coordinateDirectionList (Fin n))
      (fun y : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f y.ofLp:ℂ)) v =
      (f v.ofLp:ℂ) := by
  have hfc : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin n) => (f y.ofLp:ℂ)) :=
    (hf.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedEmbedding).comp_left
      Complex.ofReal_zero
  have hF : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => (f y.ofLp:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hfs.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff)
  have hT : ∀ y∈tsupport (fun y : EuclideanSpace ℝ (Fin n) => (f y.ofLp:ℂ)),
      ∀ i, y i≤tau := by
    intro y hy i
    have hsub := tsupport_comp_subset (g := (Complex.ofReal : ℝ → ℂ)) Complex.ofReal_zero
      (fun y : EuclideanSpace ℝ (Fin n) => f y.ofLp)
    have hp := tsupport_comp_subset_preimage f (EuclideanSpace.equiv (Fin n) ℝ).continuous
    exact profile_coordinate_upper hsupp y.ofLp (hp (hsub hy)) i
  have hh := complexCumulativeExtension_signed_full n tau _ hfc hF hT v hv
  rw [complexCumulativeExtension_ofReal] at hh
  convert hh using 1
  congr 2

theorem appendMeasurableEquiv_measurePreserving (n m : ℕ) :
    MeasurePreserving (appendMeasurableEquiv n m) := by
  let e := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (n+m) => ℝ) finSumFinEquiv)
  have he : appendMeasurableEquiv n m=e := by
    ext p i
    change Fin.append p.1 p.2 i = e p i
    cases i using Fin.addCases with
    | left i => simp [e,MeasurableEquiv.coe_piCongrLeft,
        MeasurableEquiv.coe_sumPiEquivProdPi_symm,Equiv.piCongrLeft]
    | right i => simp [e,MeasurableEquiv.coe_piCongrLeft,
        MeasurableEquiv.coe_sumPiEquivProdPi_symm,Equiv.piCongrLeft]
  rw [he]
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin (n+m) => ℝ) finSumFinEquiv).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Fin m => ℝ))

theorem tensorProfile_tsupport {n m : ℕ} {a b : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin m → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n a) (hg : tsupport g ⊆ positiveSimplex m b) :
    tsupport (tensorProfile f g) ⊆ positiveSimplex (n+m) (a+b) := by
  intro v hv
  have hleft : (fun i : Fin n => v (i.castAdd m)) ∈ tsupport f := by
    exact tsupport_comp_subset_preimage (f := fun x : Fin (n+m) → ℝ =>
      fun i : Fin n => x (i.castAdd m)) f
      (continuous_pi (fun i => continuous_apply _)) (tsupport_mul_subset_left hv)
  have hright : (fun i : Fin m => v (i.natAdd n)) ∈ tsupport g := by
    exact tsupport_comp_subset_preimage (f := fun x : Fin (n+m) → ℝ =>
      fun i : Fin m => x (i.natAdd n)) g
      (continuous_pi (fun i => continuous_apply _)) (tsupport_mul_subset_right hv)
  refine ⟨?_,?_⟩
  · intro i
    cases i using Fin.addCases with
    | left i => exact (hf hleft).1 i
    | right i => exact (hg hright).1 i
  · change (∑ i, v i)<a+b
    rw [Fin.sum_univ_add]
    exact add_lt_add (hf hleft).2 (hg hright).2

theorem tensorProfile_tail {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (v : Fin n → ℝ) (w : Fin m → ℝ) :
    (∫ y in Ici (Fin.append v w), tensorProfile f g y) =
      (∫ y in Ici v, f y)*(∫ y in Ici w, g y) := by
  have hd : (appendMeasurableEquiv n m) ⁻¹' Ici (Fin.append v w) = (Ici v) ×ˢ (Ici w) := by
    ext p
    change (∀ i, Fin.append v w i≤Fin.append p.1 p.2 i) ↔ _
    constructor
    · intro h
      exact ⟨fun i => by simpa using h (i.castAdd m),fun i => by simpa using h (i.natAdd n)⟩
    · rintro ⟨h1,h2⟩ i
      cases i using Fin.addCases with
      | left i => simpa using h1 i
      | right i => simpa using h2 i
  have hm := (appendMeasurableEquiv_measurePreserving n m).setIntegral_preimage_emb
    (appendMeasurableEquiv n m).measurableEmbedding (tensorProfile f g) (Ici (Fin.append v w))
  rw [hd] at hm
  rw [← hm]
  simp only [appendMeasurableEquiv_apply,tensorProfile_append]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod_mul f g

theorem cumulativeProfile_tensor {n m : ℕ} {a b : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin m → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n a) (hg : tsupport g ⊆ positiveSimplex m b)
    (v : Fin n → ℝ) (w : Fin m → ℝ) (hv : ∀ i, 0≤v i) (hw : ∀ i, 0≤w i) :
    cumulativeProfile (a+b) (tensorProfile f g) (Fin.append v w) =
      cumulativeProfile a f v*cumulativeProfile b g w := by
  rw [cumulativeProfile_tail (a+b) _ (tensorProfile_tsupport f g hf hg),
    cumulativeProfile_tail a f hf _ hv,cumulativeProfile_tail b g hg _ hw,tensorProfile_tail]
  intro i
  cases i using Fin.addCases with
  | left i => simpa using hv i
  | right i => simpa using hw i

theorem divisorSum_tensor (X M : ℕ) {n m : ℕ}
    (F : (Fin n → ℝ) → ℝ) (G : (Fin m → ℝ) → ℝ) (b : Fin n → ℕ) (c : Fin m → ℕ) :
    divisorSum X (tensorProfile F G) M (Fin.append b c)=
      divisorSum X F M b*divisorSum X G M c := by
  classical
  unfold divisorSum
  rw [Finset.sum_mul_sum, ←Finset.sum_product']
  symm
  apply Finset.sum_equiv (Fin.appendEquiv n m)
  · intro p
    simp only [Finset.mem_product,Fintype.mem_piFinset,Fin.appendEquiv_apply]
    constructor
    · rintro ⟨h1,h2⟩ i
      cases i using Fin.addCases with
      | left i => simpa using h1 i
      | right i => simpa using h2 i
    · intro h
      exact ⟨fun i => by simpa using h (i.castAdd m),fun i => by simpa using h (i.natAdd n)⟩
  · intro p _
    exact (divisorCoefficient_tensor X F G p.1 p.2).symm

theorem divisorSum_congr_orthant {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ℕ} (hX : 2≤X) (M : ℕ) (b : ι → ℕ) (F G : (ι → ℝ) → ℝ)
    (hFG : ∀ v, (∀ i, 0≤v i) → F v=G v) : divisorSum X F M b=divisorSum X G M b := by
  apply Finset.sum_congr rfl
  intro d hd
  unfold divisorCoefficient
  congr 1
  apply hFG
  apply logCoordinates_nonneg hX
  intro i
  exact Nat.pos_of_mem_divisors ((Fintype.mem_piFinset.mp hd) i)

theorem divisorSum_cumulative_tensor {n m : ℕ} {a b : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin m → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n a) (hg : tsupport g ⊆ positiveSimplex m b)
    {X : ℕ} (hX : 2≤X) (M : ℕ) (s : Fin n → ℕ) (t : Fin m → ℕ) :
    divisorSum X (cumulativeProfile (a+b) (tensorProfile f g)) M (Fin.append s t)=
      divisorSum X (cumulativeProfile a f) M s*divisorSum X (cumulativeProfile b g) M t := by
  rw [←divisorSum_tensor]
  apply divisorSum_congr_orthant hX
  intro v hv
  let v1 : Fin n → ℝ := fun i => v (i.castAdd m)
  let v2 : Fin m → ℝ := fun i => v (i.natAdd n)
  have he : v=Fin.append v1 v2 := by ext i; cases i using Fin.addCases <;> simp [v1,v2]
  rw [he,tensorProfile_append]
  exact cumulativeProfile_tensor f g hf hg v1 v2 (fun i => hv _) (fun i => hv _)

theorem divisorCoefficient_snoc_one (X : ℕ) {n : ℕ}
    (F : (Fin (n+1) → ℝ) → ℝ) (d : Fin n → ℕ) :
    divisorCoefficient X F (Fin.snoc d 1)=
      divisorCoefficient X (fun v => F (Fin.snoc v 0)) d := by
  simp [divisorCoefficient,logCoordinates_snoc,Fin.prod_univ_castSucc]

theorem divisorCoefficient_snoc_prime_zero {X M a n : ℕ} (hX : 2≤X) (hM : X<M+a)
    (F : (Fin (n+1) → ℝ) → ℝ) {rho : ℝ} (hrho : rho<1) (hb : HasBudget F rho)
    (d : Fin n → ℕ) (hd : ∀ i, 0<d i) : divisorCoefficient X F (Fin.snoc d (M+a))=0 := by
  have hp : 0<M+a := by omega
  have hcoord := logCoordinates_nonneg hX (d := Fin.snoc d (M+a)) (by
    intro i; cases i using Fin.lastCases <;> simp [hp,hd])
  have hs : rho<∑ i,logCoordinates X (Fin.snoc d (M+a)) i := by
    apply hrho.trans
    apply lt_of_lt_of_le _ (Finset.single_le_sum (fun i _ => hcoord i) (Finset.mem_univ (Fin.last n)))
    simp only [logCoordinates,Fin.snoc_last]
    apply (lt_div_iff₀ (log_pos_of_two_le hX)).mpr
    simpa only [one_mul] using Real.log_lt_log (by exact_mod_cast (by omega : 0<X))
      (by exact_mod_cast hM)
  rw [divisorCoefficient,hb _ hcoord hs,mul_zero]

theorem divisorSum_snoc (X M : ℕ) {n : ℕ} (F : (Fin (n+1) → ℝ) → ℝ)
    (b : Fin n → ℕ) (a : ℕ) :
    divisorSum X F M (Fin.snoc b a)=
      ∑ r∈(M+a).divisors, ∑ d∈Fintype.piFinset (fun i => (M+b i).divisors),
        divisorCoefficient X F (Fin.snoc d r) := by
  classical
  unfold divisorSum
  rw [←Finset.sum_product']
  symm
  apply Finset.sum_equiv (Fin.snocEquiv (fun _ : Fin (n+1) => ℕ))
  · intro p
    simp only [Finset.mem_product,Fintype.mem_piFinset,Fin.snocEquiv]
    constructor
    · rintro ⟨h1,h2⟩ i
      cases i using Fin.lastCases with
      | last => simpa using h1
      | cast i => simpa using h2 i
    · intro h
      exact ⟨by simpa using h (Fin.last n),fun i => by simpa using h i.castSucc⟩
  · intro p _
    rfl

theorem divisorSum_prime_delete {X M a n : ℕ} (hX : 2≤X) (hM : X<M+a)
    (hp : Nat.Prime (M+a)) (F : (Fin (n+1) → ℝ) → ℝ)
    {rho : ℝ} (hrho : rho<1) (hb : HasBudget F rho) (b : Fin n → ℕ) :
    divisorSum X F M (Fin.snoc b a)=divisorSum X (fun v => F (Fin.snoc v 0)) M b := by
  rw [divisorSum_snoc,hp.divisors]
  rw [Finset.sum_insert (by simpa using hp.ne_one.symm),Finset.sum_singleton]
  have hz : (∑ d∈Fintype.piFinset (fun i => (M+b i).divisors),
      divisorCoefficient X F (Fin.snoc d (M+a)))=0 := by
    apply Finset.sum_eq_zero
    intro d hd
    exact divisorCoefficient_snoc_prime_zero hX hM F hrho hb d
      (fun i => Nat.pos_of_mem_divisors ((Fintype.mem_piFinset.mp hd) i))
  rw [hz,add_zero]
  apply Finset.sum_congr rfl
  intro d _
  exact divisorCoefficient_snoc_one X F d

theorem rayVector_fiber_nonneg {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (y : doubleFibers b R → ℝ) (hy : ∀ r, 0≤y r) (i : ι) :
    0≤rayVector (fun r : doubleFibers b R => fiberRay b r.val) y i := by
  classical
  simp only [rayVector,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,fiberRay_apply]
  exact Finset.sum_nonneg (fun r _ => mul_nonneg (hy r) (by split_ifs <;> norm_num))

theorem rayVector_singleton_zero {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (i : ι)
    (hi : (Finset.univ.filter fun j => b j=b i).card=1)
    (y : doubleFibers b R → ℝ) :
    rayVector (fun r : doubleFibers b R => fiberRay b r.val) y i=0 := by
  classical
  simp only [rayVector,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,fiberRay_apply]
  apply Finset.sum_eq_zero
  intro r _
  have hr : b i≠r.val := by
    intro he
    have hh := (Finset.mem_filter.mp r.property).2
    rw [←he,hi] at hh
    norm_num at hh
  simp [hr]

theorem cumulativeProfile_kernel_small_fibers {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau)
    {α : Type*} (b : Fin n → α) (R : Finset α) (hR : ∀ i,b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin n))
      (fun v => (cumulativeProfile tau f v.ofLp:ℂ)) hF hFs) (fiberSubsetFamily b R) =
      ∫ y, (f (rayVector (fun r : doubleFibers b R => fiberRay b r.val) y).ofLp:ℂ)
        ∂positiveOrthantMeasure (doubleFibers b R) := by
  rw [small_fiber_kernelConstant b R hR hcard]
  apply integral_congr_ae
  rw [positiveOrthantMeasure_eq_restrict]
  filter_upwards [ae_restrict_mem (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioi))] with y hy
  exact cumulativeProfile_signed_full tau f hf hfs hsupp _
    (rayVector_fiber_nonneg b R y (fun r => (hy r (Set.mem_univ r)).le))

theorem cumulativeProfile_kernel_singleton_zero {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau)
    {α : Type*} (b : Fin n → α) (R : Finset α) (hR : ∀ i,b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2)
    (i : Fin n) (hi : (Finset.univ.filter fun j => b j=b i).card=1)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin n))
      (fun v => (cumulativeProfile tau f v.ofLp:ℂ)) hF hFs) (fiberSubsetFamily b R)=0 := by
  rw [cumulativeProfile_kernel_small_fibers f hf hfs hsupp b R hR hcard]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  have hz : f (rayVector (fun r : doubleFibers b R => fiberRay b r.val) y).ofLp=0 := by
    by_contra hne
    have hh := (hsupp (subset_tsupport f hne)).1 i
    have he := rayVector_singleton_zero b R i hi y
    change 0<rayVector (fun r : doubleFibers b R => fiberRay b r.val) y i at hh
    rw [he] at hh
    exact lt_irrefl _ hh
  simp [hz]

theorem castAdd_ne_addNat_self {n : ℕ} (i j : Fin n) : i.castAdd n ≠ j.addNat n := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_addNat] at hval
  omega

theorem addNat_ne_castAdd_self {n : ℕ} (i j : Fin n) : i.addNat n ≠ j.castAdd n :=
  (castAdd_ne_addNat_self j i).symm

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_EqualityPatterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem fiberSubsetFamily_image_eq_of_kernel {ι α β : Type*} [Fintype ι]
    (a : ι → α) (b : ι → β) (hab : ∀ i j, a i=a j ↔ b i=b j) :
    fiberSubsetFamily a (Finset.univ.image a)=fiberSubsetFamily b (Finset.univ.image b) := by
  classical
  ext S
  simp only [mem_fiberSubsetFamily_image]
  constructor <;> rintro ⟨hS,h⟩
  · exact ⟨hS,fun i hi j hj => (hab i j).mp (h i hi j hj)⟩
  · exact ⟨hS,fun i hi j hj => (hab i j).mpr (h i hi j hj)⟩

theorem append_fiber_card {m n : ℕ} {α : Type*} (a : Fin m → α) (b : Fin n → α) (r : α) :
    (Finset.univ.filter fun i => Fin.append a b i=r).card=
      (Finset.univ.filter fun i => a i=r).card+(Finset.univ.filter fun i => b i=r).card := by
  classical
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Fin.sum_univ_add,Fin.append_left,Fin.append_right]

theorem append_fiber_card_le_two {m n : ℕ} {α : Type*}
    (a : Fin m → α) (b : Fin n → α) (ha : Function.Injective a) (hb : Function.Injective b) (r : α) :
    (Finset.univ.filter fun i => Fin.append a b i=r).card≤2 := by
  classical
  rw [append_fiber_card]
  have h1 : (Finset.univ.filter fun i => a i=r).card≤1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact ha ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  have h2 : (Finset.univ.filter fun i => b i=r).card≤1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact hb ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  omega

theorem append_left_singleton {m n : ℕ} {α : Type*}
    (a : Fin m → α) (b : Fin n → α) (ha : Function.Injective a)
    (i : Fin m) (hi : a i∉Set.range b) :
    (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.castAdd n)).card=1 := by
  classical
  have he : (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.castAdd n))=
      {i.castAdd n} := by
    ext j
    cases j using Fin.addCases with
    | left j => simp [ha.eq_iff]
    | right j =>
      have hn : b j≠a i := fun h => hi ⟨j,h⟩
      have hne : Fin.natAdd m j≠i.castAdd n := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
        omega
      simp [hn,hne]
  rw [he,Finset.card_singleton]

theorem append_right_singleton {m n : ℕ} {α : Type*}
    (a : Fin m → α) (b : Fin n → α) (hb : Function.Injective b)
    (i : Fin n) (hi : b i∉Set.range a) :
    (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.natAdd m)).card=1 := by
  classical
  have he : (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b (i.natAdd m))=
      {i.natAdd m} := by
    ext j
    cases j using Fin.addCases with
    | left j =>
      have hn : a j≠b i := fun h => hi ⟨j,h⟩
      have hne : j.castAdd n≠Fin.natAdd m i := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
        omega
      simp [hn,hne]
    | right j => simp [hb.eq_iff]
  rw [he,Finset.card_singleton]

theorem cumulative_tensor_unmatched_kernel_zero {m n : ℕ} {tau : ℝ}
    (f : (Fin m → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f ⊆ positiveSimplex m tau) (hsg : tsupport g ⊆ positiveSimplex n tau)
    {α : Type*} (a : Fin m → α) (b : Fin n → α)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : Set.range a≠Set.range b)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (m+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f g) v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (m+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f g) v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin (m+n)))
      (fun v => (cumulativeProfile (tau+tau) (tensorProfile f g) v.ofLp:ℂ)) hF hFs)
      (fiberSubsetFamily (Fin.append a b) (Finset.univ.image (Fin.append a b)))=0 := by
  classical
  have hh : ∃ i : Fin (m+n),
      (Finset.univ.filter fun j => Fin.append a b j=Fin.append a b i).card=1 := by
    by_cases hsub : Set.range a⊆Set.range b
    · have hnot : ¬Set.range b⊆Set.range a := fun h => hab (Set.Subset.antisymm hsub h)
      obtain ⟨v,⟨i,rfl⟩,hi⟩ := Set.not_subset.mp hnot
      exact ⟨i.natAdd m,append_right_singleton a b hb i hi⟩
    · obtain ⟨v,⟨i,rfl⟩,hi⟩ := Set.not_subset.mp hsub
      exact ⟨i.castAdd n,append_left_singleton a b ha i hi⟩
  obtain ⟨i,hi⟩ := hh
  exact cumulativeProfile_kernel_singleton_zero (tensorProfile f g)
    (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs)
    (tensorProfile_tsupport f g hsf hsg) (Fin.append a b) _
    (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ _))
    (fun r _ => append_fiber_card_le_two a b ha hb r) i hi hF hFs

theorem numericPattern_ker {ι : Type*} [Fintype ι] (r : Setoid ι) :
    Setoid.ker (numericPattern r)=r := by
  apply Setoid.ext
  intro i j
  change (Fintype.equivFin (Quotient r) (Quotient.mk r i)).val=
    (Fintype.equivFin (Quotient r) (Quotient.mk r j)).val ↔ r i j
  rw [Fin.val_inj,(Fintype.equivFin (Quotient r)).injective.eq_iff,Quotient.eq]

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_Detectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem ker_comp_injective {ι α β : Type*} (b : ι → α) (f : α → β) (hf : Function.Injective f) :
    Setoid.ker (f∘b)=Setoid.ker b := by
  apply Setoid.ext
  intro i j
  exact hf.eq_iff

theorem divisorSum_fin_zero (X M : ℕ) (F : (Fin 0 → ℝ) → ℝ) (b : Fin 0 → ℕ) :
    divisorSum X F M b=F 0 := by
  classical
  have h : Fintype.piFinset (fun i => (M+b i).divisors)={(0 : Fin 0 → ℕ)} := by
    ext d
    simp [funext_iff]
  rw [divisorSum,h,Finset.sum_singleton]
  simp only [divisorCoefficient,Fin.prod_univ_zero,one_mul]
  congr 1
  ext i
  exact Fin.elim0 i

theorem divisorSum_singleton_at_prime {X M b : ℕ} (hX : 2≤X) (hM : X<M+b)
    (hp : Nat.Prime (M+b)) (G : (Fin 1 → ℝ) → ℝ) {rho : ℝ}
    (hrho : rho<1) (hbudget : HasBudget G rho) :
    divisorSum X G M (fun _ => b)=G 0 := by
  have ht : (fun _ : Fin 1 => b)=Fin.snoc (0 : Fin 0 → ℕ) b := by ext i; fin_cases i; rfl
  rw [ht,divisorSum_prime_delete hX hM hp G hrho hbudget,divisorSum_fin_zero]
  congr 1

theorem theta_div_log_le_upper {X M b Y : ℕ} (hX : 2≤X) (hY : M+b≤Y) (hYP : 1≤Y) :
    theta (M+b)/Real.log X≤Real.log Y/Real.log X := by
  apply div_le_div_of_nonneg_right _ (log_pos_of_two_le hX).le
  by_cases hp : Nat.Prime (M+b)
  · rw [theta,ite_eq_left hp]
    exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hY)
  · rw [theta,ite_eq_right hp]
    exact Real.log_nonneg (by exact_mod_cast hYP)

theorem singleton_divisor_majorant {X M b Y : ℕ} (hX : 2≤X) (hM : X<M+b)
    (hY : M+b≤Y) (hYP : 1≤Y) (G : (Fin 1 → ℝ) → ℝ) {rho : ℝ}
    (hrho : rho<1) (hbudget : HasBudget G rho) (hG : G 0=1) :
    theta (M+b)/Real.log X≤(Real.log Y/Real.log X)*divisorSum X G M (fun _ => b)^2 := by
  by_cases hp : Nat.Prime (M+b)
  · rw [divisorSum_singleton_at_prime hX hM hp G hrho hbudget,hG,one_pow,mul_one]
    exact theta_div_log_le_upper hX hY hYP
  · rw [theta,ite_eq_right hp,zero_div]
    exact mul_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast hYP))
      (log_pos_of_two_le hX).le) (sq_nonneg _)

theorem sum_square_diagonal_offdiag {α : Type*} [DecidableEq α]
    (B : Finset α) (f : α → ℝ) :
    (∑ b∈B,f b)^2=(∑ b∈B,f b^2)+∑ b∈B,∑ c∈B.erase b,f b*f c := by
  rw [pow_two,Finset.sum_mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [←Finset.sum_erase_add B (fun c => f b*f c) hb]
  ring

theorem detector_square_majorant {X M Y : ℕ} (hX : 2≤X) (hYP : 1≤Y)
    (B : Finset ℕ) (hM : ∀ b∈B, X<M+b) (hY : ∀ b∈B, M+b≤Y)
    (G : (Fin 1 → ℝ) → ℝ) {rho : ℝ}
    (hrho : rho<1) (hbudget : HasBudget G rho) (hG : G 0=1) :
    detector X B M^2≤(Real.log Y/Real.log X)*detector X B M+
      (Real.log Y/Real.log X)^2*∑ b∈B,∑ c∈B.erase b,
        divisorSum X G M (fun _ => b)^2*divisorSum X G M (fun _ => c)^2 := by
  classical
  let t := fun b => theta (M+b)/Real.log X
  let q := Real.log Y/Real.log X
  let D := fun b => divisorSum X G M (fun _ => b)
  have ht (b : ℕ) : 0≤t b := div_nonneg (theta_nonneg _) (log_pos_of_two_le hX).le
  have hq : 0≤q := div_nonneg (Real.log_nonneg (by exact_mod_cast hYP)) (log_pos_of_two_le hX).le
  have he : detector X B M=∑ b∈B,t b := by rw [detector,Finset.sum_div]
  have hupper (b : ℕ) (hb : b∈B) : t b≤q := theta_div_log_le_upper hX (hY b hb) hYP
  have hmajor (b : ℕ) (hb : b∈B) : t b≤q*(D b)^2 :=
    singleton_divisor_majorant hX (hM b hb) (hY b hb) hYP G hrho hbudget hG
  rw [he,sum_square_diagonal_offdiag,Finset.mul_sum,Finset.mul_sum]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro b hb
    simpa only [pow_two] using mul_le_mul_of_nonneg_right (hupper b hb) (ht b)
  · apply Finset.sum_le_sum
    intro b hb
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c hc
    have hcB := Finset.mem_of_mem_erase hc
    have hh := mul_le_mul (hmajor b hb) (hmajor c hcB) (ht c)
      (mul_nonneg hq (sq_nonneg (D b)))
    dsimp [q,D] at hh
    nlinarith

theorem average_mono {X : ℕ} (f g : ℕ → ℝ)
    (h : ∀ m∈Finset.Ioc X (2*X),f m≤g m) : average X f≤average X g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg X)

theorem average_add (X : ℕ) (f g : ℕ → ℝ) :
    average X (fun m => f m+g m)=average X f+average X g := by
  rw [average,Finset.sum_add_distrib,add_div]
  rfl

theorem average_const_mul (X : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    average X (fun m => c*f m)=c*average X f := by
  simp only [average,←Finset.mul_sum,mul_div_assoc]

theorem average_finset_sum {α : Type*} (X : ℕ) (S : Finset α) (f : α → ℕ → ℝ) :
    average X (fun m => ∑ i∈S,f i m)=∑ i∈S,average X (f i) := by
  unfold average
  rw [Finset.sum_comm,Finset.sum_div]

theorem weighted_detector_square_majorant {X Y : ℕ} (hX : 2≤X) (hYP : 1≤Y)
    (B : Finset ℕ) (hM : ∀ m ∈ Finset.Ioc X (2*X), ∀ b ∈ B, X < m+b)
    (hY : ∀ m ∈ Finset.Ioc X (2*X), ∀ b ∈ B, m+b ≤ Y)
    (W : ℕ → ℝ) (hW : ∀ m∈Finset.Ioc X (2*X),0≤W m)
    (G : (Fin 1 → ℝ) → ℝ) {rho : ℝ}
    (hrho : rho<1) (hbudget : HasBudget G rho) (hG : G 0=1) :
    average X (fun m => W m*detector X B m^2)≤
      (Real.log Y/Real.log X)*average X (fun m => W m*detector X B m)+
      (Real.log Y/Real.log X)^2*∑ b∈B,∑ c∈B.erase b,
        average X (fun m => W m*divisorSum X G m (fun _ => b)^2*
          divisorSum X G m (fun _ => c)^2) := by
  classical
  have hh := average_mono (X:=X) (fun m => W m*detector X B m^2)
    (fun m => W m*((Real.log Y/Real.log X)*detector X B m+
      (Real.log Y/Real.log X)^2*∑ b∈B,∑ c∈B.erase b,
        divisorSum X G m (fun _ => b)^2*divisorSum X G m (fun _ => c)^2)) (by
      intro m hm
      exact mul_le_mul_of_nonneg_left (detector_square_majorant hX hYP B
        (hM m hm) (hY m hm) G hrho hbudget hG) (hW m hm))
  have he : (fun m => W m*((Real.log Y/Real.log X)*detector X B m+
      (Real.log Y/Real.log X)^2*∑ b∈B,∑ c∈B.erase b,
        divisorSum X G m (fun _ => b)^2*divisorSum X G m (fun _ => c)^2))=
      (fun m => (Real.log Y/Real.log X)*(W m*detector X B m)+
        (Real.log Y/Real.log X)^2*(∑ b∈B,∑ c∈B.erase b,
          W m*divisorSum X G m (fun _ => b)^2*divisorSum X G m (fun _ => c)^2)) := by
    funext m
    have hs : (∑ b∈B,∑ c∈B.erase b,
        W m*divisorSum X G m (fun _ => b)^2*divisorSum X G m (fun _ => c)^2)=
        W m*(∑ b∈B,∑ c∈B.erase b,
          divisorSum X G m (fun _ => b)^2*divisorSum X G m (fun _ => c)^2) := by
      simp only [Finset.mul_sum,mul_assoc]
    rw [hs]
    ring
  rw [he,average_add,average_const_mul,average_const_mul,
    average_finset_sum] at hh
  simpa only [average_finset_sum] using hh

theorem detector_log_ratio_tendsto {lam : ℝ} (hlam : 0≤lam) :
    Tendsto (fun X : ℕ => Real.log (2*X+2*blockLength lam X)/Real.log X) atTop (𝓝 1) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun X : ℕ => (Real.log (X:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hH : Tendsto (fun X : ℕ => (blockLength lam X:ℝ)/(X:ℝ)) atTop (𝓝 0) := by
    have hlogratio : Tendsto (fun X : ℕ => Real.log (X:ℝ)/(X:ℝ)) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
    apply squeeze_zero' (Eventually.of_forall (fun X => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    · filter_upwards [eventually_ge_atTop 2] with X hX
      exact div_le_div_of_nonneg_right (blockLength_le_mul_log hlam hX) (Nat.cast_nonneg X)
    · simpa only [mul_div_assoc,mul_zero] using hlogratio.const_mul lam
  have harg : Tendsto (fun X : ℕ => 2+2*(blockLength lam X:ℝ)/(X:ℝ)) atTop (𝓝 2) := by
    simpa only [mul_zero,add_zero,mul_div_assoc] using tendsto_const_nhds.add (hH.const_mul 2)
  have hh := ((Real.continuousAt_log (by norm_num : (2:ℝ)≠0)).tendsto.comp harg).mul hinv
  have hh' := (tendsto_const_nhds (x := (1:ℝ))).add hh
  simp only [mul_zero,add_zero] at hh'
  apply hh'.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hXP : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hL := log_pos_of_two_le hX
  have hA : 0<2+2*(blockLength lam X:ℝ)/(X:ℝ) := by positivity
  have he : (2*(X:ℝ)+2*blockLength lam X)=(X:ℝ)*(2+2*(blockLength lam X:ℝ)/(X:ℝ)) := by
    field_simp
  simp only [Function.comp_apply]
  rw [he,Real.log_mul hXP.ne' hA.ne',add_div,div_self hL.ne']
  rfl

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_PatternMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem permutedLabels_fiber_sum {n : ℕ} (e : Equiv.Perm (Fin n)) (r : Fin n) {K : Type*} [AddCommMonoid K]
    (w : Fin (n+n) → K) :
    (∑ i∈Finset.univ.filter (fun i => permutedLabels e i=r), w i)=w (r.castAdd n)+w ((e.symm r).natAdd n) := by
  classical
  rw [Finset.sum_filter,Fin.sum_univ_add]
  simp [permutedLabels,←Equiv.eq_symm_apply]

@[simp] theorem permutedLabels_fiber_card {n : ℕ} (e : Equiv.Perm (Fin n)) (r : Fin n) :
    (Finset.univ.filter fun i => permutedLabels e i=r).card=2 := by
  simpa using permutedLabels_fiber_sum e r (fun _ => (1:ℕ))

theorem permutedLabels_classical_fiber {n : ℕ} (e : Equiv.Perm (Fin n)) (r : Fin n) :
    @Finset.filter (Fin (n+n)) (fun i => permutedLabels e i=r)
      (fun _ => Classical.propDecidable _) Finset.univ =
      Finset.univ.filter (fun i => permutedLabels e i=r) := by
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

theorem permutedLabels_kernel {n : ℕ} (e : Equiv.Perm (Fin n)) (w : Fin (n+n) → ℂ) :
    familyKernel (fiberSubsetFamily (permutedLabels e) Finset.univ) w =
      (∏ i,w i)*(∏ i : Fin n,(w (i.castAdd n)+w ((e.symm i).natAdd n))⁻¹) := by
  rw [familyKernel_small_fibers (permutedLabels e) Finset.univ (fun i => Finset.mem_univ _) (by
    intro r _
    rw [permutedLabels_classical_fiber,permutedLabels_fiber_card])]
  simp only [permutedLabels_classical_fiber,permutedLabels_fiber_card,Finset.filter_true,
    permutedLabels_fiber_sum]

theorem permutedRay_frequency {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) (u : EuclideanSpace ℝ (Fin (n+n))) :
    laplaceFrequency (fourierCoordinateSum (Fin (n+n))) (permutedRay e i) u =
      frequencyW (u (i.castAdd n))+frequencyW (u ((e.symm i).natAdd n)) := by
  unfold permutedRay
  simp only [laplaceFrequency,map_add,inner_add_right,Complex.ofReal_add,
    fourierCoordinateSum_apply]
  simp [frequencyW,EuclideanSpace.inner_single_right]
  ring

theorem permutedRay_positive {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    0<fourierCoordinateSum (Fin (n+n)) (permutedRay e i) := by
  have h := congrArg Complex.re (permutedRay_frequency e i 0)
  simp only [laplaceFrequency_re,Complex.add_re,frequencyW_re] at h
  rw [h]
  norm_num

theorem rayVector_permuted {n : ℕ} (e : Equiv.Perm (Fin n)) (y : Fin n → ℝ) :
    (rayVector (permutedRay e) y).ofLp=Fin.append y (y ∘ e) := by
  classical
  ext i
  cases i using Fin.addCases with
  | left i => simp [rayVector,permutedRay,WithLp.ofLp_sum,Finset.sum_apply,
      smul_eq_mul,Pi.single_apply,Finset.sum_add_distrib,castAdd_ne_addNat_self]
  | right i =>
    have he (x : Fin n) : i=e.symm x ↔ x=e i := by
      constructor
      · intro h; rw [h]; simp
      · intro h; rw [h]; simp
    simp [rayVector,permutedRay,WithLp.ofLp_sum,Finset.sum_apply,
      smul_eq_mul,Pi.single_apply,Finset.sum_add_distrib,addNat_ne_castAdd_self,he]

theorem permuted_kernelConstant {n : ℕ} (e : Equiv.Perm (Fin n))
    (F : EuclideanSpace ℝ (Fin (n+n)) → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+n))) F hF hFs)
      (fiberSubsetFamily (permutedLabels e) Finset.univ) =
      ∫ y, signedDirections (coordinateDirectionList (Fin (n+n))) F (rayVector (permutedRay e) y)
        ∂positiveOrthantMeasure (Fin n) := by
  rw [←sourceFourier_derivative_laplace (fourierCoordinateSum (Fin (n+n)))
    (coordinateDirectionList (Fin (n+n))) F hF hFs (permutedRay e) (permutedRay_positive e)]
  unfold kernelConstant
  apply integral_congr_ae
  filter_upwards [] with u
  rw [contourKernel,permutedLabels_kernel,coordinateDirectionList_multiplier]
  simp only [permutedRay_frequency,mul_assoc]

theorem injective_same_range_perm {n : ℕ} {α : Type*}
    (a b : Fin n → α) (hb : Function.Injective b)
    (hab : Set.range a=Set.range b) : ∃ e : Equiv.Perm (Fin n), b=a ∘ e := by
  classical
  have hs : ∀ i,∃ j,a j=b i := by
    intro i
    have : b i ∈ Set.range a := hab.symm ▸ Set.mem_range_self i
    exact this
  choose e he using hs
  have hei : Function.Injective e := by
    intro i j hij
    apply hb
    rw [←he i,←he j,hij]
  exact ⟨Equiv.ofBijective e ⟨hei,Finite.surjective_of_injective hei⟩,by funext i; exact (he i).symm⟩

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_WeightMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

@[simp] theorem weightedBlock_zero (X h a m : ℕ)
    (F : (Fin 0 → ℝ) → ℝ) (k : Setoid (Fin 0) → ℝ) :
    weightedBlock X h a F k m=k ⊥*F 0 := by
  unfold weightedBlock
  simp only [divisorSum_fin_zero]
  have he (b : Fin 0 → Fin h) : Setoid.ker b=⊥ := by
    apply Setoid.ext
    intro i
    exact Fin.elim0 i
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,pow_zero,one_nsmul]

theorem matchedPattern_injective {n : ℕ} : Function.Injective (@matchedPattern n) := by
  intro e f hef
  apply Equiv.ext
  intro i
  have he : (matchedPattern e) ((e i).castAdd n) (i.natAdd n) := by
    change permutedLabels e ((e i).castAdd n)=permutedLabels e (i.natAdd n)
    simp [permutedLabels]
  rw [hef] at he
  change permutedLabels f ((e i).castAdd n)=permutedLabels f (i.natAdd n) at he
  simpa [permutedLabels] using he

theorem matchedPattern_quotient_card {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Fintype.card (Quotient (matchedPattern e))=n := by
  have hs : Function.Surjective (permutedLabels e) := by
    intro j
    exact ⟨j.castAdd n,by simp [permutedLabels]⟩
  have eqv : Quotient (matchedPattern e) ≃ Fin n :=
    Setoid.quotientKerEquivOfSurjective (permutedLabels e) hs
  exact (Fintype.card_congr eqv).trans (Fintype.card_fin n)

theorem ker_eq_bot_iff_injective {α β : Type*} (f : α → β) :
    Setoid.ker f=⊥ ↔ Function.Injective f := by
  constructor
  · intro h x y hxy
    change (Setoid.ker f) x y at hxy
    rw [h] at hxy
    exact hxy
  · intro h
    apply Setoid.ext
    intro x y
    exact h.eq_iff

theorem numericPattern_left_injective {m n : ℕ} (r : Setoid (Fin (m+n)))
    (h : Setoid.comap (Fin.castAdd n) r=⊥) :
    Function.Injective (fun i : Fin m => numericPattern r (i.castAdd n)) := by
  apply (ker_eq_bot_iff_injective _).mp
  have he : Setoid.ker (fun i : Fin m => numericPattern r (i.castAdd n))=
      Setoid.comap (Fin.castAdd n) (Setoid.ker (numericPattern r)) := rfl
  rw [he,numericPattern_ker,h]

theorem numericPattern_right_injective {m n : ℕ} (r : Setoid (Fin (m+n)))
    (h : Setoid.comap (Fin.natAdd m) r=⊥) :
    Function.Injective (fun i : Fin n => numericPattern r (i.natAdd m)) := by
  apply (ker_eq_bot_iff_injective _).mp
  have he : Setoid.ker (fun i : Fin n => numericPattern r (i.natAdd m))=
      Setoid.comap (Fin.natAdd m) (Setoid.ker (numericPattern r)) := rfl
  rw [he,numericPattern_ker,h]

theorem injective_ranges_card {m n : ℕ} {α : Type*} (a : Fin m → α) (b : Fin n → α)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : Set.range a=Set.range b) : m=n := by
  have e : Fin m ≃ Fin n := (Equiv.ofInjective a ha).trans
    ((Equiv.setCongr hab).trans (Equiv.ofInjective b hb).symm)
  simpa using Fintype.card_congr e

theorem matching_pattern_eq {n : ℕ} (r : Setoid (Fin (n+n)))
    (hleft : Setoid.comap (Fin.castAdd n) r=⊥)
    (hright : Setoid.comap (Fin.natAdd n) r=⊥)
    (hrange : Set.range (fun i : Fin n => numericPattern r (i.castAdd n))=
      Set.range (fun i : Fin n => numericPattern r (i.natAdd n))) :
    ∃ e : Equiv.Perm (Fin n),r=matchedPattern e := by
  let a := fun i : Fin n => numericPattern r (i.castAdd n)
  let b := fun i : Fin n => numericPattern r (i.natAdd n)
  have ha : Function.Injective a := numericPattern_left_injective r hleft
  have hb : Function.Injective b := numericPattern_right_injective r hright
  obtain ⟨e,he⟩ := injective_same_range_perm a b hb hrange
  refine ⟨e,?_⟩
  rw [←numericPattern_ker r]
  have hf : numericPattern r=a ∘ permutedLabels e := by
    funext i
    cases i using Fin.addCases with
    | left i => simp [a,permutedLabels]
    | right i => simpa [b,permutedLabels] using congrFun he i
  rw [hf,ker_comp_injective _ _ ha]
  rfl

theorem sum_matched_patterns {n : ℕ} (c : ℂ) (A : Setoid (Fin (n+n)) → ℂ)
    (hzero : ∀ r,r∉Set.range (@matchedPattern n) → A r=0)
    (hvalue : ∀ e : Equiv.Perm (Fin n),A (matchedPattern e)=c) :
    (∑ r,A r)=(n.factorial:ℂ)*c := by
  classical
  calc
    _ = ∑ r∈Finset.univ.image (@matchedPattern n),A r := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro r _ hr
      apply hzero r
      rintro ⟨e,rfl⟩
      exact hr (Finset.mem_image_of_mem _ (Finset.mem_univ e))
    _ = ∑ e : Equiv.Perm (Fin n),A (matchedPattern e) :=
      Finset.sum_image (fun _ _ _ _ h => matchedPattern_injective h)
    _ = _ := by simp [hvalue,Fintype.card_perm]

@[simp] theorem cumulativeProfile_fin_zero {tau : ℝ} (f : (Fin 0 → ℝ) → ℝ)
    (hsf : tsupport f⊆positiveSimplex 0 tau) (v : Fin 0 → ℝ) :
    cumulativeProfile tau f v=f 0 := by
  rw [cumulativeProfile_tail tau f hsf v (fun i => Fin.elim0 i)]
  rw [Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  have he : Ici v=(Set.univ : Set (Fin 0 → ℝ)) := by
    ext x
    simp only [Set.mem_Ici,Set.mem_univ,iff_true]
    exact fun i => Fin.elim0 i
  rw [he,setIntegral_univ]
  exact integral_dirac f 0

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_ProfileSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem cumulativeProfile_perm_orthant {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hsupp : tsupport f⊆positiveSimplex n tau)
    (hsym : SymmetricFunction f) (e : Equiv.Perm (Fin n))
    (v : Fin n → ℝ) (hv : ∀ i,0≤v i) :
    cumulativeProfile tau f (v ∘ e)=cumulativeProfile tau f v := by
  change cumulativeProfile tau f (fun i => v (e i))=cumulativeProfile tau f v
  rw [cumulativeProfile_tail tau f hsupp _ (fun i => hv (e i)),
    cumulativeProfile_tail tau f hsupp _ hv]
  let q := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e.symm
  have hq : MeasurePreserving q volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) e.symm
  have hq_apply (x : Fin n → ℝ) : q x=x ∘ e := by
    funext i
    simp [q,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  have he : q ⁻¹' {x : Fin n → ℝ | ∀ i,v (e i)≤x i}={x : Fin n → ℝ | ∀ i,v i≤x i} := by
    ext x
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,hq_apply,Function.comp_apply]
    constructor
    · intro h i
      simpa using h (e.symm i)
    · intro h i
      exact h (e i)
  have hh := hq.integral_comp' (fun x => ({x : Fin n → ℝ | ∀ i,v (e i)≤x i}).indicator f x)
  have hefun : (fun x => ({x : Fin n → ℝ | ∀ i,v (e i)≤x i}).indicator f (q x))=
      ({x : Fin n → ℝ | ∀ i,v i≤x i}).indicator f := by
    funext x
    have hx : (∀ i,v (e i)≤q x i) ↔ ∀ i,v i≤x i := by
      simpa only [Set.mem_preimage,Set.mem_ofPred_eq] using
        (Set.ext_iff.mp he x)
    have hm : q x∈{x : Fin n → ℝ | ∀ i,v (e i)≤x i} ↔ x∈{x : Fin n → ℝ | ∀ i,v i≤x i} := hx
    by_cases hvx : x∈{x : Fin n → ℝ | ∀ i,v i≤x i}
    · rw [Set.indicator_of_mem (hm.mpr hvx),Set.indicator_of_mem hvx,hq_apply,hsym]
    · rw [Set.indicator_of_notMem (fun h => hvx (hm.mp h)),Set.indicator_of_notMem hvx]
  rw [hefun,integral_indicator (by measurability), integral_indicator (by measurability)] at hh
  exact hh.symm

theorem divisorSum_perm_orthant {n X m : ℕ} (hX : 2≤X)
    (F : (Fin n → ℝ) → ℝ)
    (hF : ∀ (e : Equiv.Perm (Fin n)) v,(∀ i,0≤v i) → F (v ∘ e)=F v)
    (e : Equiv.Perm (Fin n)) (b : Fin n → ℕ) :
    divisorSum X F m (b ∘ e)=divisorSum X F m b := by
  classical
  unfold divisorSum
  symm
  apply Finset.sum_equiv (functionPerm e)
  · intro d
    simp only [Fintype.mem_piFinset,functionPerm,Equiv.coe_fn_mk,Function.comp_apply]
    exact e.surjective.forall
  · intro d hd
    change divisorCoefficient X F d=divisorCoefficient X F (d ∘ e)
    unfold divisorCoefficient
    have hp : ∀ i,0<d i := fun i => Nat.pos_of_mem_divisors ((Fintype.mem_piFinset.mp hd) i)
    have he : logCoordinates X (d ∘ e)=(logCoordinates X d) ∘ e := rfl
    rw [he,hF e _ (logCoordinates_nonneg hX hp)]
    congr 1
    exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm

theorem subsetEnumeration_image {h n : ℕ} (S : {S : Finset (Fin h) // S.card=n}) :
    Finset.univ.image (subsetEnumeration S)=S.1 := by
  classical
  ext x
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    exact (S.1.orderIsoOfFin S.2 i).2
  · intro hx
    refine ⟨(S.1.orderIsoOfFin S.2).symm ⟨x,hx⟩,?_⟩
    change ((S.1.orderIsoOfFin S.2) ((S.1.orderIsoOfFin S.2).symm ⟨x,hx⟩)).val=x
    simp

theorem enumeratePerm_image {h n : ℕ}
    (t : {S : Finset (Fin h) // S.card=n} × Equiv.Perm (Fin n)) :
    Finset.univ.image (enumeratePerm t).val=t.1.1 := by
  classical
  rw [←subsetEnumeration_image t.1]
  ext x
  simp only [Finset.mem_image,Finset.mem_univ,true_and,enumeratePerm,Function.comp_apply]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨t.2 i,hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨t.2.symm i,by simpa using hi⟩

theorem enumeratePerm_bijective (h n : ℕ) :
    Function.Bijective (enumeratePerm (h:=h) (n:=n)) := by
  classical
  constructor
  · rintro ⟨S,e⟩ ⟨T,d⟩ he
    have hST : S=T := by
      apply Subtype.ext
      rw [←enumeratePerm_image (S,e),←enumeratePerm_image (T,d),he]
    subst T
    have hed : e=d := by
      apply Equiv.ext
      intro i
      apply (subsetEnumeration S).injective
      exact congrFun (congrArg Subtype.val he) i
    subst d
    rfl
  · intro b
    let S : {S : Finset (Fin h) // S.card=n} :=
      ⟨Finset.univ.image b.val,by rw [Finset.card_image_of_injective _ b.2]; simp⟩
    have he : Set.range (subsetEnumeration S)=Set.range b.val := by
      ext x
      have hh := Finset.ext_iff.mp (subsetEnumeration_image S) x
      simpa only [Finset.mem_image,Finset.mem_univ,true_and,S,Set.mem_range] using hh
    obtain ⟨e,he⟩ := injective_same_range_perm (subsetEnumeration S) b.val b.2 he
    exact ⟨(S,e),Subtype.ext he.symm⟩

theorem weightedBlock_eq_unordered {n X h a m : ℕ} (hX : 2≤X)
    (F : (Fin n → ℝ) → ℝ)
    (hsym : ∀ (e : Equiv.Perm (Fin n)) v,(∀ i,0≤v i) → F (v ∘ e)=F v) :
    weightedBlock X h a F (subsetCoefficient n) m=unorderedBlock X h a F m := by
  classical
  unfold weightedBlock
  have he : (∑ b : Fin n → Fin h, subsetCoefficient n (Setoid.ker b)*
      divisorSum X F m (fun i => a+(b i:ℕ)))=
      ∑ b : {b : Fin n → Fin h // Function.Injective b},
        (n.factorial:ℝ)⁻¹*divisorSum X F m (fun i => a+(b.val i:ℕ)) := by
    simp only [subsetCoefficient,Setoid.ker_eq_bot_iff,ite_mul,zero_mul]
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype (p:=fun b : Fin n → Fin h => Function.Injective b)
      (Finset.univ.filter fun b : Fin n → Fin h => Function.Injective b) (by simp) _
  rw [he]
  rw [←Fintype.sum_equiv (Equiv.ofBijective enumeratePerm (enumeratePerm_bijective h n))
    (fun t => (n.factorial:ℝ)⁻¹*divisorSum X F m (fun i => a+((enumeratePerm t).val i:ℕ)))
    _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  unfold unorderedBlock
  apply Finset.sum_congr rfl
  intro S _
  have hd (e : Equiv.Perm (Fin n)) :
      divisorSum X F m (fun i => a+((enumeratePerm (S,e)).val i:ℕ))=
      divisorSum X F m (fun i => a+(subsetEnumeration S i:ℕ)) :=
    divisorSum_perm_orthant hX F hsym e (fun i => a+(subsetEnumeration S i:ℕ))
  simp only [hd,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
  have hn : (n.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

theorem orderedWeight_eq_unordered {tau lam : ℝ} {k X : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (hX : 2≤X) (m : ℕ) : orderedWeight tau lam k f X m=unorderedWeight tau lam k f X m := by
  unfold orderedWeight unorderedWeight
  apply Finset.sum_congr rfl
  intro j _
  have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
  exact weightedBlock_eq_unordered hX _ (cumulativeProfile_perm_orthant _ hfj.2.2.1 hfj.2.2.2)

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_RestrictedWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem cumulative_tensor_permuted_kernel_invariant {n : ℕ} (e : Equiv.Perm (Fin n)) {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau) (hsym : ∀ y, f (y ∘ e)=f y)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+n)))
      (fun v => (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)) hF hFs)
      (fiberSubsetFamily (permutedLabels e) Finset.univ) = (l2Mass f:ℂ) := by
  rw [permuted_kernelConstant]
  have he : (∫ y, signedDirections (coordinateDirectionList (Fin (n+n)))
      (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
        (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)) (rayVector (permutedRay e) y)
      ∂positiveOrthantMeasure (Fin n)) =
      ∫ y, (f y^2:ℂ) ∂positiveOrthantMeasure (Fin n) := by
    apply integral_congr_ae
    rw [positiveOrthantMeasure_eq_restrict]
    filter_upwards [ae_restrict_mem (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioi))] with y hy
    rw [cumulativeProfile_signed_full (tau+tau) (tensorProfile f f)
      (tensorProfile_compact f f hf hf) (tensorProfile_smooth f f hfs hfs)
      (tensorProfile_tsupport f f hsupp hsupp)]
    · rw [rayVector_permuted,tensorProfile_append,hsym,pow_two]
      simp only [Complex.ofReal_mul]
    · intro i
      rw [rayVector_permuted]
      cases i using Fin.addCases with
      | left i => simpa using (hy i (Set.mem_univ i)).le
      | right i => simpa using (hy (e i) (Set.mem_univ (e i))).le
  rw [he]
  simp_rw [←Complex.ofReal_pow]
  rw [integral_complex_ofReal,positiveOrthantMeasure_eq_restrict]
  congr 1
  unfold l2Mass
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hfz : f y=0 := by
    by_contra hne
    exact hy (fun i _ => (hsupp (subset_tsupport f hne)).1 i)
  simp [hfz]

theorem l2Mass_tensor {n d : ℕ} (f : (Fin n → ℝ) → ℝ) (g : (Fin d → ℝ) → ℝ) :
    l2Mass (tensorProfile f g)=l2Mass f*l2Mass g := by
  unfold l2Mass
  rw [←(appendMeasurableEquiv_measurePreserving n d).integral_comp
    (appendMeasurableEquiv n d).measurableEmbedding]
  simp only [appendMeasurableEquiv_apply,tensorProfile_append,mul_pow]
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul (fun x => f x^2) (fun y => g y^2)

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_PairedDetectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem tensorProfile_extendPerm {n d : ℕ} (e : Equiv.Perm (Fin n))
    (f : (Fin n → ℝ) → ℝ) (g : (Fin d → ℝ) → ℝ)
    (hf : ∀ y,f (y ∘ e)=f y) (v : Fin (n+d) → ℝ) :
    tensorProfile f g (v ∘ extendPerm e d)=tensorProfile f g v := by
  simp only [tensorProfile,Function.comp_apply,extendPerm_left,extendPerm_right]
  congr 1
  exact hf (fun i => v (i.castAdd d))

theorem extendLabels_injective {n : ℕ} {α : Type*} (a : Fin n → α) (d : ℕ)
    (ha : Function.Injective a) : Function.Injective (extendLabels a d) := by
  intro i j h
  cases i using Fin.addCases <;> cases j using Fin.addCases <;>
    simp only [extendLabels_left,extendLabels_right,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,Sum.inr_ne_inl] at h
  · exact congrArg (Fin.castAdd d) (ha h)
  · exact congrArg (Fin.natAdd n) h

theorem extendLabels_range_ne {n p : ℕ} {α : Type*} (a : Fin n → α) (b : Fin p → α)
    (d : ℕ) (hab : Set.range a≠Set.range b) :
    Set.range (extendLabels a d)≠Set.range (extendLabels b d) := by
  intro he
  apply hab
  ext x
  have hh : ∀ {n : ℕ} (a : Fin n → α), Sum.inl x∈Set.range (extendLabels a d) ↔ x∈Set.range a := by
    intro n a
    constructor
    · rintro ⟨i,hi⟩
      cases i using Fin.addCases with
      | left i => exact ⟨i,by simpa using hi⟩
      | right i => simp at hi
    · rintro ⟨i,rfl⟩; exact ⟨i.castAdd d,by simp⟩
  rw [←hh a,←hh b,he]

theorem castAdd_ne_natAdd {n d : ℕ} (i : Fin n) (j : Fin d) : i.castAdd d≠j.natAdd n := by
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hh
  have hi := i.isLt
  omega

theorem natAdd_ne_castAdd {n d : ℕ} (i : Fin d) (j : Fin n) : i.natAdd n≠j.castAdd d :=
  (castAdd_ne_natAdd j i).symm

theorem extraPairFamily_matched {n d : ℕ} (e : Equiv.Perm (Fin n)) :
    extraPairFamily (n:=n) (p:=n) (matchedPattern e) d=
      fiberSubsetFamily (permutedLabels (extendPerm e d)) Finset.univ := by
  classical
  have he := fiberSubsetFamily_image_eq_of_kernel (extraPairLabels (n:=n) (p:=n) (matchedPattern e) d)
    (permutedLabels (extendPerm e d))
  have hh : ∀ i j, extraPairLabels (n:=n) (p:=n) (matchedPattern e) d i=extraPairLabels (n:=n) (p:=n) (matchedPattern e) d j ↔
      permutedLabels (extendPerm e d) i=permutedLabels (extendPerm e d) j := by
    intro i j
    have hr (i j : Fin (n+n)) : numericPattern (matchedPattern e) i=numericPattern (matchedPattern e) j ↔
        permutedLabels e i=permutedLabels e j := by
      change (Setoid.ker (numericPattern (matchedPattern e))) i j ↔ _
      rw [numericPattern_ker]
      rfl
    cases i using Fin.addCases <;> cases j using Fin.addCases <;>
      simp only [extraPairLabels,Fin.append_left,Fin.append_right,permutedLabels] <;>
      rename_i i j <;> cases i using Fin.addCases <;> cases j using Fin.addCases <;>
      simp only [extendLabels_left,extendLabels_right,extendPerm_left,extendPerm_right,
        Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,Fin.castAdd_inj,Fin.natAdd_inj,
        hr,permutedLabels,Fin.append_left,Fin.append_right,Function.id_def,Equiv.apply_eq_iff_eq,
        castAdd_ne_natAdd,natAdd_ne_castAdd]
  have he' : extraPairFamily (matchedPattern e) d=
      fiberSubsetFamily (permutedLabels (extendPerm e d))
        (Finset.univ.image (permutedLabels (extendPerm e d))) := by
    ext S
    simpa only [extraPairFamily,mem_fiberSubsetFamily_image] using Finset.ext_iff.mp (he hh) S
  rw [he']
  congr 1
  ext i
  simp only [Finset.mem_image,Finset.mem_univ,true_and,iff_true]
  exact ⟨i.castAdd (n+d),by simp [permutedLabels]⟩

theorem extraPairKernel_unmatched {n p d : ℕ} {tau sigma : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (hw : HasCompactSupport w)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g) (hws : ContDiff ℝ ∞ w)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau)
    (hsw : tsupport w⊆positiveSimplex d sigma)
    (r : Setoid (Fin (n+p)))
    (hl : Setoid.comap (Fin.castAdd p) r=⊥) (hr : Setoid.comap (Fin.natAdd n) r=⊥)
    (hne : Set.range (fun i : Fin n => numericPattern r (i.castAdd p))≠
      Set.range (fun i : Fin p => numericPattern r (i.natAdd n))) :
    extraPairKernel tau sigma f g w hf hg hw hfs hgs hws r=0 := by
  unfold extraPairKernel
  convert cumulative_tensor_unmatched_kernel_zero (tensorProfile f w) (tensorProfile g w)
    (tensorProfile_compact f w hf hw) (tensorProfile_compact g w hg hw)
    (tensorProfile_smooth f w hfs hws) (tensorProfile_smooth g w hgs hws)
    (tensorProfile_tsupport f w hsf hsw) (tensorProfile_tsupport g w hsg hsw)
    (extendLabels _ d) (extendLabels _ d)
    (extendLabels_injective _ d (numericPattern_left_injective r hl))
    (extendLabels_injective _ d (numericPattern_right_injective r hr))
    (extendLabels_range_ne _ _ d hne)
    (realEuclidean_compact _ (cumulativeProfile_compact _ _ (extraPairProfile_compact f g w hf hg hw)))
    (realEuclidean_smooth _ (cumulativeProfile_smooth _ _ (extraPairProfile_compact f g w hf hg hw)
      (extraPairProfile_smooth f g w hfs hgs hws))) using 1
  congr 2
  ext x
  simp only [extraPairFamily,extraPairLabels,mem_fiberSubsetFamily_image]

theorem extraPairKernel_matched {n d : ℕ} {tau sigma : ℝ}
    (f : (Fin n → ℝ) → ℝ) (w : (Fin d → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hw : HasCompactSupport w)
    (hfs : ContDiff ℝ ∞ f) (hws : ContDiff ℝ ∞ w)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsw : tsupport w⊆positiveSimplex d sigma)
    (hsym : SymmetricFunction f) (e : Equiv.Perm (Fin n)) :
    extraPairKernel tau sigma f f w hf hf hw hfs hfs hws (matchedPattern e)=
      (l2Mass f*l2Mass w:ℂ) := by
  unfold extraPairKernel
  rw [extraPairFamily_matched]
  have hh := cumulative_tensor_permuted_kernel_invariant (extendPerm e d) (tensorProfile f w)
    (tensorProfile_compact f w hf hw) (tensorProfile_smooth f w hfs hws)
    (tensorProfile_tsupport f w hsf hsw) (tensorProfile_extendPerm e f w (fun y => hsym e y))
    (realEuclidean_compact _ (cumulativeProfile_compact _ _ (extraPairProfile_compact f f w hf hf hw)))
    (realEuclidean_smooth _ (cumulativeProfile_smooth _ _ (extraPairProfile_compact f f w hf hf hw)
      (extraPairProfile_smooth f f w hfs hfs hws)))
  rw [l2Mass_tensor,Complex.ofReal_mul] at hh
  convert hh using 1
  rfl

theorem extra_square_pattern_sum {n d : ℕ} {tau sigma : ℝ} (lam : ℝ)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsym : SymmetricFunction f)
    (w : (Fin d → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆positiveSimplex d sigma) :
    (∑ r : Setoid (Fin (n+n)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*extraPairKernel tau sigma f f w hf hf hw hfs hfs hws r))=
      (alpha lam n*l2Mass f*l2Mass w:ℂ) := by
  classical
  let A := fun r : Setoid (Fin (n+n)) =>
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*extraPairKernel tau sigma f f w hf hf hw hfs hfs hws r)
  have hz : ∀ r,r∉Set.range (@matchedPattern n) → A r=0 := by
    intro r hr
    by_cases hl : Setoid.comap (Fin.castAdd n) r=⊥
    · by_cases hr' : Setoid.comap (Fin.natAdd n) r=⊥
      · have hne : Set.range (fun i : Fin n => numericPattern r (i.castAdd n))≠
            Set.range (fun i : Fin n => numericPattern r (i.natAdd n)) := by
          intro he
          obtain ⟨e,rfl⟩ := matching_pattern_eq r hl hr' he
          exact hr ⟨e,rfl⟩
        simp only [A,extraPairKernel_unmatched f f w hf hf hw hfs hfs hws hsf hsf hsw r hl hr' hne,mul_zero]
      · simp only [A,tensorCoefficient,subsetCoefficient,ite_eq_right hr',mul_zero,Complex.ofReal_zero,zero_mul]
    · simp only [A,tensorCoefficient,subsetCoefficient,ite_eq_right hl,zero_mul,Complex.ofReal_zero]
  have hv : ∀ e : Equiv.Perm (Fin n), A (matchedPattern e)=
      ((n.factorial:ℂ)⁻¹)^2*((lam:ℂ)^n*((l2Mass f:ℂ)*(l2Mass w:ℂ))) := by
    intro e
    simp only [A,tensorCoefficient,matchedPattern_left,matchedPattern_right,subsetCoefficient,
      ↓reduceIte,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast,
      matchedPattern_quotient_card,extraPairKernel_matched f w hf hw hfs hws hsf hsw hsym e,Complex.ofReal_mul,pow_two]
  have hh := sum_matched_patterns _ A hz hv
  change (∑ r,A r)=_
  rw [hh]
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  simp only [alpha,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
  field_simp

theorem extra_cross_pattern_sum {m n d : ℕ} (hmn : m≠n) {tau sigma : ℝ} (lam : ℝ)
    (f : (Fin m → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex m tau) (hsg : tsupport g⊆positiveSimplex n tau)
    (w : (Fin d → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆positiveSimplex d sigma) :
    (∑ r : Setoid (Fin (m+n)),
      (tensorCoefficient (subsetCoefficient m) (subsetCoefficient n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*extraPairKernel tau sigma f g w hf hg hw hfs hgs hws r))=0 := by
  apply Finset.sum_eq_zero
  intro r _
  by_cases hl : Setoid.comap (Fin.castAdd n) r=⊥
  · by_cases hr : Setoid.comap (Fin.natAdd m) r=⊥
    · have hne : Set.range (fun i : Fin m => numericPattern r (i.castAdd n))≠
          Set.range (fun i : Fin n => numericPattern r (i.natAdd m)) := by
        intro he
        exact hmn (injective_ranges_card _ _ (numericPattern_left_injective r hl)
          (numericPattern_right_injective r hr) he)
      rw [extraPairKernel_unmatched f g w hf hg hw hfs hgs hws hsf hsg hsw r hl hr hne,mul_zero,mul_zero]
    · simp only [tensorCoefficient,subsetCoefficient,ite_eq_right hr,mul_zero,Complex.ofReal_zero,zero_mul]
  · simp only [tensorCoefficient,subsetCoefficient,ite_eq_right hl,zero_mul,Complex.ofReal_zero]

theorem extraAverage_finset_sum {d : ℕ} {α : Type*} (X h : ℕ) (S : Finset α)
    (H : α → ℕ → ℝ) (W : (Fin d → ℝ) → ℝ) :
    extraAverage X h (fun m => ∑ i∈S,H i m) W=∑ i∈S,extraAverage X h (H i) W := by
  unfold extraAverage
  simp only [Finset.sum_mul,average_finset_sum]
  rw [Finset.sum_comm]

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_DetectorMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem extra_cumulative_square_limit {n d : ℕ} {tau sigma lam : ℝ}
    (htau : 0≤tau) (hsigma : 0 ≤ sigma) (hbudget : 2*(tau+sigma)<1) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsym : SymmetricFunction f)
    (w : (Fin (d+1) → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆positiveSimplex (d+1) sigma) :
    Tendsto (fun X : ℕ => extraAverage X (blockLength lam X) (fun m =>
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) m^2)
      (cumulativeProfile sigma w)) atTop
      (𝓝 (lam^(d+1)*alpha lam n*l2Mass f*l2Mass w)) := by
  have hh := extra_cumulative_pair_limit htau hsigma hbudget hlam f f hf hf hfs hfs hsf hsf w hw hws hsw
  rw [extra_square_pattern_sum lam f hf hfs hsf hsym w hw hws hsw] at hh
  have hh' := Complex.continuous_re.continuousAt.tendsto.comp hh
  simpa [Function.comp_def,←Complex.ofReal_pow,Complex.mul_re,←pow_two,mul_assoc] using hh'

theorem extra_cumulative_cross_limit {n p d : ℕ} (hnp : n≠p) {tau sigma lam : ℝ}
    (htau : 0≤tau) (hsigma : 0 ≤ sigma) (hbudget : 2*(tau+sigma)<1) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau)
    (w : (Fin (d+1) → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆positiveSimplex (d+1) sigma) :
    Tendsto (fun X : ℕ => extraAverage X (blockLength lam X) (fun m =>
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) m*
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau g) (subsetCoefficient p) m)
      (cumulativeProfile sigma w)) atTop (𝓝 0) := by
  have hh := extra_cumulative_pair_limit htau hsigma hbudget hlam f g hf hg hfs hgs hsf hsg w hw hws hsw
  rw [extra_cross_pattern_sum hnp lam f g hf hg hfs hgs hsf hsg w hw hws hsw,mul_zero] at hh
  exact Complex.continuous_re.continuousAt.tendsto.comp hh

theorem orderedWeight_extra_limit {tau sigma lam : ℝ} {k d : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (hsigma : 0 ≤ sigma) (hbudget : 2*(tau+sigma)<1) (hlam : 0<lam)
    (w : (Fin (d+1) → ℝ) → ℝ) (hw : HasCompactSupport w) (hws : ContDiff ℝ ∞ w)
    (hsw : tsupport w⊆positiveSimplex (d+1) sigma) :
    Tendsto (fun X : ℕ => extraAverage X (blockLength lam X) (fun m => orderedWeight tau lam k f X m^2)
      (cumulativeProfile sigma w)) atTop (𝓝 (lam^(d+1)*l2Mass w*familyW lam k f)) := by
  classical
  let H := fun (j : Fin (k+1)) X m => weightedBlock X (blockLength lam X) (blockLength lam X+1)
       (cumulativeProfile tau (f j)) (subsetCoefficient j) m
  have hp (i j : Fin (k+1)) :
      Tendsto (fun X : ℕ => extraAverage X (blockLength lam X) (fun m => H i X m*H j X m)
        (cumulativeProfile sigma w)) atTop
        (𝓝 (if i=j then lam^(d+1)*alpha lam i*l2Mass (f i)*l2Mass w else 0)) := by
    have hfi := hf.2.1 i (by omega : (i:ℕ)≤k)
    have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
    by_cases hij : i=j
    · subst j
      simp only [↓reduceIte]
      simpa only [H,pow_two] using extra_cumulative_square_limit htau hsigma hbudget hlam
        (f i) hfi.2.1 hfi.1 hfi.2.2.1 hfi.2.2.2 w hw hws hsw
    · simp only [ite_eq_right hij]
      have hne : (i:ℕ)≠(j:ℕ) := fun h => hij (Fin.ext h)
      exact extra_cumulative_cross_limit hne htau hsigma hbudget hlam
        (f i) (f j) hfi.2.1 hfj.2.1 hfi.1 hfj.1 hfi.2.2.1 hfj.2.2.1 w hw hws hsw
  have hs := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => hp i j
  have he (X : ℕ) : extraAverage X (blockLength lam X) (fun m => orderedWeight tau lam k f X m^2)
      (cumulativeProfile sigma w)=
      ∑ i : Fin (k+1),∑ j : Fin (k+1),extraAverage X (blockLength lam X) (fun m => H i X m*H j X m)
        (cumulativeProfile sigma w) := by
    unfold orderedWeight
    simp only [pow_two,Finset.sum_mul_sum,extraAverage_finset_sum]
    rfl
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte] at hs
  have hv : (∑ i : Fin (k+1),lam^(d+1)*alpha lam i*l2Mass (f i)*l2Mass w)=
      lam^(d+1)*l2Mass w*familyW lam k f := by
    have he : ∀ i : Fin (k+1),lam^(d+1)*alpha lam i*l2Mass (f i)*l2Mass w=
        (lam^(d+1)*l2Mass w)*(alpha lam i*l2Mass (f i)) := fun _ => by ring
    simp only [he,←Finset.mul_sum]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => alpha lam j*l2Mass (f j)) (k+1)
  rw [hv] at hs
  exact hs.congr' (Eventually.of_forall fun X => (he X).symm)

theorem distinctBox_pair_iff {h : ℕ} (b : Fin 2 → Fin h) :
    b∈distinctBox (fun _ => (1:ℤ)) ↔ b 0≠b 1 := by
  simp only [distinctBox,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hb he
    have hh : boxTuple (fun _ => (1:ℤ)) b 0=boxTuple (fun _ => (1:ℤ)) b 1 := by simp only [boxTuple,he]
    have hi := hb hh
    exact (by decide : (0:Fin 2)≠1) hi
  · intro hb i j hij
    have he : b i=b j := by
      apply Fin.ext
      exact_mod_cast (add_left_cancel (show (1:ℤ)+(b i:ℤ)=1+(b j:ℤ) from hij))
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (hb he)
    · exact False.elim (hb he.symm)
    · rfl

theorem sum_distinctBox_pair {h : ℕ} (F : Fin h → Fin h → ℝ) :
    (∑ v∈distinctBox (s:=2) (h:=h) (fun _ => (1:ℤ)),F (v 0) (v 1))=
      ∑ b : Fin h,∑ c : Fin h,if b≠c then F b c else 0 := by
  classical
  have he : distinctBox (s:=2) (h:=h) (fun _ => (1:ℤ))=Finset.univ.filter (fun b => b 0≠b 1) := by
    ext b
    simp only [distinctBox_pair_iff,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [he,Finset.sum_filter]
  calc
    _ = ∑ bc : Fin h × Fin h, if bc.1≠bc.2 then F bc.1 bc.2 else 0 :=
      Fintype.sum_equiv (finTwoArrowEquiv (Fin h)) _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_prod_type _

theorem sum_first_interval (h : ℕ) (F : ℕ → ℝ) :
    (∑ b∈Finset.Ioc 0 h,F b)=∑ b : Fin h,F (1+b) := by
  have he : Finset.Ioc 0 h=Finset.Ico 1 (h+1) := by
    ext b
    simp only [Finset.mem_Ioc,Finset.mem_Ico]
    omega
  rw [he,Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel,Finset.sum_range]

theorem sum_first_offdiagonal (h : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ b∈Finset.Ioc 0 h,∑ c∈(Finset.Ioc 0 h).erase b,F b c)=
      ∑ b : Fin h,∑ c : Fin h,if b≠c then F (1+b) (1+c) else 0 := by
  classical
  have he (b : ℕ) : (∑ c∈(Finset.Ioc 0 h).erase b,F b c)=
      ∑ c∈Finset.Ioc 0 h,if b≠c then F b c else 0 := by
    rw [←Finset.filter_ne,Finset.sum_filter]
  simp_rw [he,sum_first_interval]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simp only [ne_eq,Nat.add_left_cancel_iff,Fin.val_inj]

theorem extraAverage_pair_identity {tau : ℝ} {X : ℕ} (hX : 2≤X) (h : ℕ)
    (H : ℕ → ℝ) (g : (Fin 1 → ℝ) → ℝ)
    (hgs : tsupport g⊆positiveSimplex 1 tau) :
    extraAverage X h H (cumulativeProfile (tau+tau) (tensorProfile g g))=
      ∑ b∈Finset.Ioc 0 h,∑ c∈(Finset.Ioc 0 h).erase b,
        average X (fun m => H m*divisorSum X (cumulativeProfile tau g) m (fun _ => b)^2*
          divisorSum X (cumulativeProfile tau g) m (fun _ => c)^2) := by
  classical
  have hd (m : ℕ) (v : Fin 2 → Fin h) :
      divisorSum X (cumulativeProfile (tau+tau) (tensorProfile g g)) m (fun i => 1+(v i:ℕ))=
        divisorSum X (cumulativeProfile tau g) m (fun _ => 1+(v 0:ℕ))*
        divisorSum X (cumulativeProfile tau g) m (fun _ => 1+(v 1:ℕ)) := by
    convert divisorSum_cumulative_tensor g g hgs hgs hX m
      (fun _ => 1+(v 0:ℕ)) (fun _ => 1+(v 1:ℕ)) using 1
    congr 1
    funext i
    fin_cases i <;> rfl
  unfold extraAverage
  simp_rw [hd,mul_pow,←mul_assoc]
  rw [average_finset_sum]
  rw [sum_distinctBox_pair (fun b c : Fin h => average X (fun m =>
    H m*divisorSum X (cumulativeProfile tau g) m (fun _ => 1+(b:ℕ))^2*
      divisorSum X (cumulativeProfile tau g) m (fun _ => 1+(c:ℕ))^2)),
    sum_first_offdiagonal]

theorem unorderedWeight_extra_pair_limit {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (hbudget : 6*tau<1) (hlam : 0<lam)
    (g : (Fin 1 → ℝ) → ℝ) (hgc : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (hgt : tsupport g⊆positiveSimplex 1 tau) :
    Tendsto (fun X : ℕ => extraAverage X (blockLength lam X)
      (fun m => unorderedWeight tau lam k f X m^2)
      (cumulativeProfile (tau+tau) (tensorProfile g g)))
      atTop (𝓝 (lam^2*l2Mass g^2*familyW lam k f)) := by
  have hh := orderedWeight_extra_limit f hf htau (by linarith : 0≤tau+tau)
    (by linarith : 2*(tau+(tau+tau))<1) hlam (d:=1) (tensorProfile g g)
    (tensorProfile_compact g g hgc hgc) (tensorProfile_smooth g g hgs hgs)
    (tensorProfile_tsupport g g hgt hgt)
  rw [l2Mass_tensor,←pow_two] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  simp only [orderedWeight_eq_unordered f hf hX]

theorem unorderedWeight_detector_bound_oai (hBV : BombieriVinogradov) {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (hbudget : 6*tau<1) (hlam : 0<lam)
    (hw : 0<familyW lam k f)
    (g : (Fin 1 → ℝ) → ℝ) (hgc : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (hgt : tsupport g⊆positiveSimplex 1 tau) (hg0 : cumulativeProfile tau g 0=1) :
    ∀ᶠ X : ℕ in atTop,
      average X (fun m => unorderedWeight tau lam k f X m^2*
        detector X (Finset.Ioc 0 (blockLength lam X)) m^2)≤
      (lam+lam^2*l2Mass g^2+1)*familyW lam k f := by
  let q := fun X : ℕ => Real.log (2*X+2*blockLength lam X)/Real.log X
  let Z := unorderedWeight tau lam k f
  let E := fun X : ℕ => extraAverage X (blockLength lam X) (fun m => Z X m^2)
    (cumulativeProfile (tau+tau) (tensorProfile g g))
  have hlim := ((detector_log_ratio_tendsto hlam.le).mul
    (unorderedWeight_external_marked_limit hBV f hf htau (by linarith) hlam)).add
    (((detector_log_ratio_tendsto hlam.le).pow 2).mul
      (unorderedWeight_extra_pair_limit f hf htau hbudget hlam g hgc hgs hgt))
  simp only [one_mul,one_pow] at hlim
  have hlim' : Tendsto (fun X : ℕ => q X*average X (fun m => Z X m^2*
      detector X (Finset.Ioc 0 (blockLength lam X)) m)+q X^2*E X)
      atTop (𝓝 ((lam+lam^2*l2Mass g^2)*familyW lam k f)) := by
    convert hlim using 1
    congr 1
    ring
  have hstrict : (lam+lam^2*l2Mass g^2)*familyW lam k f<
      (lam+lam^2*l2Mass g^2+1)*familyW lam k f := by nlinarith
  have hu := hlim'.eventually_lt_const hstrict
  filter_upwards [eventually_ge_atTop 2,hu] with X hX hU
  apply le_trans _ hU.le
  have hh := weighted_detector_square_majorant (X:=X) (Y:=2*X+2*blockLength lam X)
    hX (by omega) (Finset.Ioc 0 (blockLength lam X))
    (by intro m hm b hb; have := Finset.mem_Ioc.mp hm; have := Finset.mem_Ioc.mp hb; omega)
    (by intro m hm b hb; have := Finset.mem_Ioc.mp hm; have := Finset.mem_Ioc.mp hb; omega)
    (fun m => Z X m^2) (fun _ _ => sq_nonneg _) (cumulativeProfile tau g)
    (by linarith : tau<1) (cumulativeProfile_budget tau g hgt) hg0
  rw [←extraAverage_pair_identity hX (blockLength lam X) (fun m => Z X m^2) g hgt] at hh
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,q,E] using hh

end LargePrimeGaps

end OAI
end

theorem solution : type_of% @OAI.LargePrimeGaps.unorderedWeight_detector_bound_oai := @OAI.LargePrimeGaps.unorderedWeight_detector_bound_oai
