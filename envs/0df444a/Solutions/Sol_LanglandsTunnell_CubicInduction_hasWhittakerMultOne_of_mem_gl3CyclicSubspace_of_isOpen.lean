-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.hasWhittakerMultOne_of_mem_gl3CyclicSubspace_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/3af57300-c80b-5394-8dda-24b77c83a550

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_hasWhittakerMultOne_of_mem_gl3CyclicSubspace_of_isOpen

set_option autoImplicit false

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gl3AmbientRightTranslate gl3AmbientRightTranslate_apply IsGL3WhittakerFunctional gl3WhittakerFunctionalSpace GL3WhittakerUniquenessStatement gl3CyclicSubspace gl3AmbientRightTranslate_mem_gl3CyclicSubspace gl3CyclicRep HasWhittakerMultOne upperUnipotent3 upperUnipotent3_zero LocalGL3 natCast_natCard_quot_ne_zero exists_setOf_valued_sub_le_subset_of_isOpen exists_valued_le_exp exists_finset_ball_representatives upperUnipotent3_mul_upperUnipotent3 upperUnipotent3_inv_eq"
namespace TwistedCoinvariantAverage
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

private noncomputable def rootX (a : v.adicCompletion ℚ) : LocalGL3 v := upperUnipotent3 a 0 0

private noncomputable def rootY (b : v.adicCompletion ℚ) : LocalGL3 v := upperUnipotent3 0 b 0

private noncomputable def rootZ (c : v.adicCompletion ℚ) : LocalGL3 v := upperUnipotent3 0 0 c

private theorem rootX_add (a a' : v.adicCompletion ℚ) : rootX v (a + a') = rootX v a * rootX v a' := by
  simp only [rootX, upperUnipotent3_mul_upperUnipotent3]
  congr 1 <;> ring

private theorem rootY_add (b b' : v.adicCompletion ℚ) : rootY v (b + b') = rootY v b * rootY v b' := by
  simp only [rootY, upperUnipotent3_mul_upperUnipotent3]
  congr 1 <;> ring

private theorem rootZ_add (c c' : v.adicCompletion ℚ) : rootZ v (c + c') = rootZ v c * rootZ v c' := by
  simp only [rootZ, upperUnipotent3_mul_upperUnipotent3]
  congr 1 <;> ring

private theorem rootX_zero : rootX v 0 = 1 := upperUnipotent3_zero

private theorem rootY_zero : rootY v 0 = 1 := upperUnipotent3_zero

private theorem rootZ_zero : rootZ v 0 = 1 := upperUnipotent3_zero

private theorem upperUnipotent3_eq_rootX_mul (x y z : v.adicCompletion ℚ) :
    (upperUnipotent3 x y z : LocalGL3 v) = rootX v x * (rootY v y * rootZ v (z - x * y)) := by
  simp only [rootX, rootY, rootZ, upperUnipotent3_mul_upperUnipotent3]
  congr 1 <;> ring

private theorem rootX_mul_rootZ (a c : v.adicCompletion ℚ) : rootX v a * rootZ v c = rootZ v c * rootX v a := by
  simp only [rootX, rootZ, upperUnipotent3_mul_upperUnipotent3]
  congr 1 <;> ring

private theorem rootY_mul_rootZ (b c : v.adicCompletion ℚ) : rootY v b * rootZ v c = rootZ v c * rootY v b := by
  simp only [rootY, rootZ, upperUnipotent3_mul_upperUnipotent3]
  congr 1 <;> ring

private theorem rootZ_mul_rootZ (c c' : v.adicCompletion ℚ) : rootZ v c' * rootZ v c = rootZ v c * rootZ v c' := by
  rw [← rootZ_add, ← rootZ_add, add_comm]

private theorem rootY_mul_rootX (a b : v.adicCompletion ℚ) :
    rootY v b * rootX v a = rootX v a * (rootY v b * rootZ v (-(a * b))) := by
  simp only [rootX, rootY, rootZ, upperUnipotent3_mul_upperUnipotent3]
  congr 1 <;> ring

private theorem continuous_upperUnipotent3 :
    Continuous fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      (upperUnipotent3 p.1 p.2.1 p.2.2 : LocalGL3 v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop
  · simp only [upperUnipotent3_inv_eq]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop

private theorem continuous_rootX : Continuous (rootX v) :=
  (continuous_upperUnipotent3 v).comp
    (by fun_prop : Continuous fun a : v.adicCompletion ℚ => (a, (0 : v.adicCompletion ℚ), (0 : v.adicCompletion ℚ)))

private theorem continuous_rootY : Continuous (rootY v) :=
  (continuous_upperUnipotent3 v).comp
    (by fun_prop : Continuous fun b : v.adicCompletion ℚ => ((0 : v.adicCompletion ℚ), b, (0 : v.adicCompletion ℚ)))

private theorem continuous_rootZ : Continuous (rootZ v) :=
  (continuous_upperUnipotent3 v).comp
    (by fun_prop : Continuous fun c : v.adicCompletion ℚ => ((0 : v.adicCompletion ℚ), (0 : v.adicCompletion ℚ), c))

private theorem translate_mul (g h : LocalGL3 v) (f : LocalGL3 v → ℂ) :
    gl3AmbientRightTranslate (R := ℂ) (g * h) f = gl3AmbientRightTranslate g (gl3AmbientRightTranslate h f) := by
  funext x
  simp only [gl3AmbientRightTranslate_apply, mul_assoc]

private theorem exists_isOpen_forall_translate_eq {W : LocalGL3 v → ℂ}
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    {f : LocalGL3 v → ℂ} (hf : f ∈ gl3CyclicSubspace W) :
    ∃ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) ∧
      ∀ k ∈ U, gl3AmbientRightTranslate (R := ℂ) k f = f := by
  refine Submodule.span_induction (p := fun f _ => ∃ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) ∧
      ∀ k ∈ U, gl3AmbientRightTranslate (R := ℂ) k f = f) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨h, rfl⟩
    obtain ⟨Uv, hUo, hUv⟩ := hsm
    let U : Subgroup (LocalGL3 v) :=
      { carrier := {k | h⁻¹ * k * h ∈ Uv}
        mul_mem' := fun {a b} ha hb => by
          show h⁻¹ * (a * b) * h ∈ Uv
          rw [show h⁻¹ * (a * b) * h = h⁻¹ * a * h * (h⁻¹ * b * h) by group]
          exact Uv.mul_mem ha hb
        one_mem' := by
          show h⁻¹ * 1 * h ∈ Uv
          rw [mul_one, inv_mul_cancel]
          exact Uv.one_mem
        inv_mem' := fun {a} ha => by
          show h⁻¹ * a⁻¹ * h ∈ Uv
          rw [show h⁻¹ * a⁻¹ * h = (h⁻¹ * a * h)⁻¹ by group]
          exact Uv.inv_mem ha }
    refine ⟨U, ?_, fun k hk => ?_⟩
    · exact hUo.preimage (by fun_prop : Continuous fun k : LocalGL3 v => h⁻¹ * k * h)
    · have hW : gl3AmbientRightTranslate (R := ℂ) (h⁻¹ * k * h) W = W := funext fun g => hUv _ hk g
      rw [← translate_mul, show k * h = h * (h⁻¹ * k * h) by group, translate_mul, hW]
  · exact ⟨⊤, by simp, fun k _ => map_zero _⟩
  · intro f₁ f₂ _ _ h₁ h₂
    obtain ⟨U₁, hU₁, h₁⟩ := h₁
    obtain ⟨U₂, hU₂, h₂⟩ := h₂
    exact ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun k hk => by
      rw [map_add, h₁ k (Subgroup.mem_inf.mp hk).1, h₂ k (Subgroup.mem_inf.mp hk).2]⟩
  · intro c f _ h
    obtain ⟨U, hU, h⟩ := h
    exact ⟨U, hU, fun k hk => by rw [map_smul, h k hk]⟩

private theorem exists_forall_translate_eq_of_continuous {u : v.adicCompletion ℚ → LocalGL3 v}
    (hu : Continuous u) (hu0 : u 0 = 1) {f : LocalGL3 v → ℂ} {U : Subgroup (LocalGL3 v)}
    (hUo : IsOpen (U : Set (LocalGL3 v))) (hUf : ∀ k ∈ U, gl3AmbientRightTranslate (R := ℂ) k f = f) :
    ∃ m : ℤ, ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-m) →
      gl3AmbientRightTranslate (R := ℂ) (u t) f = f := by
  obtain ⟨j, hj⟩ := exists_setOf_valued_sub_le_subset_of_isOpen v (hUo.preimage hu) (x := 0)
    (show u 0 ∈ (U : Set (LocalGL3 v)) by rw [hu0]; exact U.one_mem)
  refine ⟨j, fun t ht => hUf _ (hj ?_)⟩
  show Valued.v (t - 0) ≤ WithZero.exp (-j)
  rwa [sub_zero]

private noncomputable def coinvKer (u : v.adicCompletion ℚ → LocalGL3 v) (χ : AddChar (v.adicCompletion ℚ) ℂ)
    (S : Submodule ℂ (LocalGL3 v → ℂ)) : Submodule ℂ (LocalGL3 v → ℂ) :=
  Submodule.span ℂ {d | ∃ t : v.adicCompletion ℚ, ∃ f ∈ S, d = gl3AmbientRightTranslate (R := ℂ) (u t) f - χ t • f}

private noncomputable def coinvKerN (ψ : AddChar (v.adicCompletion ℚ) ℂ) (S : Submodule ℂ (LocalGL3 v → ℂ)) :
    Submodule ℂ (LocalGL3 v → ℂ) :=
  Submodule.span ℂ {d | ∃ x y z : v.adicCompletion ℚ, ∃ f ∈ S,
    d = gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f - ψ (x + y) • f}

private theorem sub_mem_coinvKer (u : v.adicCompletion ℚ → LocalGL3 v) (χ : AddChar (v.adicCompletion ℚ) ℂ)
    {S : Submodule ℂ (LocalGL3 v → ℂ)} {f : LocalGL3 v → ℂ} (hf : f ∈ S) (t : v.adicCompletion ℚ) :
    gl3AmbientRightTranslate (R := ℂ) (u t) f - χ t • f ∈ coinvKer v u χ S :=
  Submodule.subset_span ⟨t, f, hf, rfl⟩

private theorem sub_mem_coinvKerN (ψ : AddChar (v.adicCompletion ℚ) ℂ) {S : Submodule ℂ (LocalGL3 v → ℂ)}
    {f : LocalGL3 v → ℂ} (hf : f ∈ S) (x y z : v.adicCompletion ℚ) :
    gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f - ψ (x + y) • f ∈ coinvKerN v ψ S :=
  Submodule.subset_span ⟨x, y, z, f, hf, rfl⟩

private theorem coinvKer_le {u : v.adicCompletion ℚ → LocalGL3 v} {χ : AddChar (v.adicCompletion ℚ) ℂ}
    {S : Submodule ℂ (LocalGL3 v → ℂ)} (hS : ∀ (g : LocalGL3 v) (f : LocalGL3 v → ℂ), f ∈ S →
      gl3AmbientRightTranslate (R := ℂ) g f ∈ S) :
    coinvKer v u χ S ≤ S := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨t, f, hf, rfl⟩
  exact S.sub_mem (hS _ _ hf) (S.smul_mem _ hf)

private theorem translate_mem_coinvKer {u : v.adicCompletion ℚ → LocalGL3 v}
    {χ : AddChar (v.adicCompletion ℚ) ℂ} {S : Submodule ℂ (LocalGL3 v → ℂ)}
    (hS : ∀ (g : LocalGL3 v) (f : LocalGL3 v → ℂ), f ∈ S → gl3AmbientRightTranslate (R := ℂ) g f ∈ S)
    {g : LocalGL3 v} (hg : ∀ t, g * u t = u t * g) {d : LocalGL3 v → ℂ} (hd : d ∈ coinvKer v u χ S) :
    gl3AmbientRightTranslate (R := ℂ) g d ∈ coinvKer v u χ S := by
  refine Submodule.span_induction (p := fun d _ => gl3AmbientRightTranslate (R := ℂ) g d ∈ coinvKer v u χ S)
    ?_ ?_ ?_ ?_ hd
  · rintro _ ⟨t, f, hf, rfl⟩
    rw [map_sub, map_smul, ← translate_mul, hg, translate_mul]
    exact sub_mem_coinvKer v u χ (hS _ _ hf) t
  · simp only [map_zero, Submodule.zero_mem]
  · intro d₁ d₂ _ _ h₁ h₂
    simpa only [map_add] using Submodule.add_mem _ h₁ h₂
  · intro c d _ h
    simpa only [map_smul] using Submodule.smul_mem _ c h

private theorem coinvKer_rootX_le (ψ : AddChar (v.adicCompletion ℚ) ℂ) (S : Submodule ℂ (LocalGL3 v → ℂ)) :
    coinvKer v (rootX v) ψ S ≤ coinvKerN v ψ S := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨t, f, hf, rfl⟩
  have h := sub_mem_coinvKerN v ψ hf t 0 0
  rwa [add_zero] at h

private theorem coinvKer_rootY_le (ψ : AddChar (v.adicCompletion ℚ) ℂ) (S : Submodule ℂ (LocalGL3 v → ℂ)) :
    coinvKer v (rootY v) ψ S ≤ coinvKerN v ψ S := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨t, f, hf, rfl⟩
  have h := sub_mem_coinvKerN v ψ hf 0 t 0
  rwa [zero_add] at h

private theorem coinvKer_rootZ_le (ψ : AddChar (v.adicCompletion ℚ) ℂ) (S : Submodule ℂ (LocalGL3 v → ℂ)) :
    coinvKer v (rootZ v) 1 S ≤ coinvKerN v ψ S := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨t, f, hf, rfl⟩
  have h := sub_mem_coinvKerN v ψ hf 0 0 t
  rw [add_zero, AddChar.map_zero_eq_one] at h
  rw [AddChar.one_apply]
  exact h

private theorem coinvKerN_le_sup {ψ : AddChar (v.adicCompletion ℚ) ℂ} {S : Submodule ℂ (LocalGL3 v → ℂ)}
    (hS : ∀ (g : LocalGL3 v) (f : LocalGL3 v → ℂ), f ∈ S → gl3AmbientRightTranslate (R := ℂ) g f ∈ S) :
    coinvKerN v ψ S ≤ coinvKer v (rootX v) ψ S ⊔ coinvKer v (rootY v) ψ S ⊔ coinvKer v (rootZ v) 1 S := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, y, z, f, hf, rfl⟩
  have hf₁ : gl3AmbientRightTranslate (R := ℂ) (rootZ v (z - x * y)) f ∈ S := hS _ _ hf
  have hf₂ : gl3AmbientRightTranslate (R := ℂ) (rootY v y)
      (gl3AmbientRightTranslate (R := ℂ) (rootZ v (z - x * y)) f) ∈ S :=
    hS _ _ hf₁
  have hA := sub_mem_coinvKer v (rootX v) ψ hf₂ x
  have hB := sub_mem_coinvKer v (rootY v) ψ hf₁ y
  have hC := sub_mem_coinvKer v (rootZ v) 1 hf (z - x * y)
  rw [AddChar.one_apply, one_smul] at hC
  have key : gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f - ψ (x + y) • f =
      (gl3AmbientRightTranslate (R := ℂ) (rootX v x)
          (gl3AmbientRightTranslate (R := ℂ) (rootY v y)
            (gl3AmbientRightTranslate (R := ℂ) (rootZ v (z - x * y)) f)) -
        ψ x • gl3AmbientRightTranslate (R := ℂ) (rootY v y)
          (gl3AmbientRightTranslate (R := ℂ) (rootZ v (z - x * y)) f)) +
      ψ x • (gl3AmbientRightTranslate (R := ℂ) (rootY v y)
          (gl3AmbientRightTranslate (R := ℂ) (rootZ v (z - x * y)) f) -
        ψ y • gl3AmbientRightTranslate (R := ℂ) (rootZ v (z - x * y)) f) +
      (ψ x * ψ y) • (gl3AmbientRightTranslate (R := ℂ) (rootZ v (z - x * y)) f - f) := by
    rw [upperUnipotent3_eq_rootX_mul, translate_mul, translate_mul, AddChar.map_add_eq_mul]
    module
  rw [key]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_left hA))
    (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.smul_mem _ _ hB))))
    (Submodule.mem_sup_right (Submodule.smul_mem _ _ hC))

private noncomputable def rootAverage (u : v.adicCompletion ℚ → LocalGL3 v) (χ : AddChar (v.adicCompletion ℚ) ℂ)
    (X : Finset (v.adicCompletion ℚ)) : Module.End ℂ (LocalGL3 v → ℂ) :=
  ∑ r ∈ X, χ (-r) • gl3AmbientRightTranslate (R := ℂ) (u r)

private theorem rootAverage_apply (u : v.adicCompletion ℚ → LocalGL3 v) (χ : AddChar (v.adicCompletion ℚ) ℂ)
    (X : Finset (v.adicCompletion ℚ)) (f : LocalGL3 v → ℂ) :
    rootAverage v u χ X f = ∑ r ∈ X, χ (-r) • gl3AmbientRightTranslate (R := ℂ) (u r) f := by
  simp only [rootAverage, LinearMap.sum_apply, LinearMap.smul_apply]

private theorem rootAverage_mem {u : v.adicCompletion ℚ → LocalGL3 v} {χ : AddChar (v.adicCompletion ℚ) ℂ}
    {S : Submodule ℂ (LocalGL3 v → ℂ)} (hS : ∀ (g : LocalGL3 v) (f : LocalGL3 v → ℂ), f ∈ S →
      gl3AmbientRightTranslate (R := ℂ) g f ∈ S) (X : Finset (v.adicCompletion ℚ)) {f : LocalGL3 v → ℂ}
    (hf : f ∈ S) : rootAverage v u χ X f ∈ S := by
  rw [rootAverage_apply]
  exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (hS _ _ hf)

private def IsKilled (u : v.adicCompletion ℚ → LocalGL3 v) (χ : AddChar (v.adicCompletion ℚ) ℂ)
    (d : LocalGL3 v → ℂ) : Prop :=
  ∃ k₀ m₀ : ℤ, ∀ k m : ℤ, k ≤ k₀ → m₀ ≤ m → ∀ X : Finset (v.adicCompletion ℚ),
    (∀ r ∈ X, Valued.v r ≤ WithZero.exp (-k)) →
    (∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) → ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-m)) →
    rootAverage v u χ X d = 0

private theorem sum_eq_sum_of_reps {M : Type*} [AddCommMonoid M] {Φ : v.adicCompletion ℚ → M} {k m : ℤ}
    (hconst : ∀ x y : v.adicCompletion ℚ, Valued.v (x - y) ≤ WithZero.exp (-m) → Φ x = Φ y)
    {X : Finset (v.adicCompletion ℚ)} (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-k))
    (hX' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-m))
    {X' : Finset (v.adicCompletion ℚ)} (hY : ∀ r ∈ X', Valued.v r ≤ WithZero.exp (-k))
    (hY' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X' ∧ Valued.v (x - r) ≤ WithZero.exp (-m)) :
    ∑ r ∈ X, Φ r = ∑ r ∈ X', Φ r := by
  calc ∑ r ∈ X, Φ r
      = ∑ r ∈ X, ∑ r' ∈ X', (if Valued.v (r - r') ≤ WithZero.exp (-m) then Φ r' else 0) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        obtain ⟨r', ⟨hr', hrr'⟩, huniq⟩ := hY' r (hX r hr)
        rw [Finset.sum_eq_single_of_mem r' hr', if_pos hrr']
        · exact hconst r r' hrr'
        · intro s hs hne
          exact if_neg fun h => hne (huniq s ⟨hs, h⟩)
    _ = ∑ r' ∈ X', ∑ r ∈ X, (if Valued.v (r - r') ≤ WithZero.exp (-m) then Φ r' else 0) :=
        Finset.sum_comm
    _ = ∑ r' ∈ X', Φ r' := by
        refine Finset.sum_congr rfl fun r' hr' => ?_
        obtain ⟨r, ⟨hr, hr'r⟩, huniq⟩ := hX' r' (hY r' hr')
        have hrr' : Valued.v (r - r') ≤ WithZero.exp (-m) := by
          rw [Valuation.map_sub_swap]
          exact hr'r
        rw [Finset.sum_eq_single_of_mem r hr, if_pos hrr']
        intro s hs hne
        refine if_neg fun h => hne (huniq s ⟨hs, ?_⟩)
        rw [Valuation.map_sub_swap]
        exact h

private theorem rootAverage_translate {u : v.adicCompletion ℚ → LocalGL3 v} (hu : ∀ a b, u (a + b) = u a * u b)
    (χ : AddChar (v.adicCompletion ℚ) ℂ) {k m : ℤ} {X : Finset (v.adicCompletion ℚ)}
    (hX : ∀ r ∈ X, Valued.v r ≤ WithZero.exp (-k))
    (hX' : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X ∧ Valued.v (x - r) ≤ WithZero.exp (-m))
    {t₀ : v.adicCompletion ℚ} (ht₀ : Valued.v t₀ ≤ WithZero.exp (-k)) {g : LocalGL3 v → ℂ}
    (hg : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-m) → gl3AmbientRightTranslate (R := ℂ) (u t) g = g)
    (hχ : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-m) → χ t = 1) :
    rootAverage v u χ X (gl3AmbientRightTranslate (R := ℂ) (u t₀) g) = χ t₀ • rootAverage v u χ X g := by
  classical
  have hconst : ∀ x y : v.adicCompletion ℚ, Valued.v (x - y) ≤ WithZero.exp (-m) →
      χ (-x) • gl3AmbientRightTranslate (R := ℂ) (u x) g = χ (-y) • gl3AmbientRightTranslate (R := ℂ) (u y) g := by
    intro x y hxy
    have hux : u x = u y * u (x - y) := by
      rw [← hu]
      congr 1
      ring
    have hχx : χ (-x) = χ (-y) := by
      have hx : -x = -y + -(x - y) := by ring
      have hxy' : Valued.v (-(x - y)) ≤ WithZero.exp (-m) := by
        rw [Valuation.map_neg]
        exact hxy
      rw [hx, AddChar.map_add_eq_mul, hχ _ hxy', mul_one]
    rw [hux, translate_mul, hg _ hxy, hχx]
  have hmem : ∀ r ∈ X.image (fun s => s + t₀), Valued.v r ≤ WithZero.exp (-k) := by
    intro r hr
    obtain ⟨s, hs, hsr⟩ := Finset.mem_image.1 hr
    rw [← hsr]
    exact Valuation.map_add_le _ (hX s hs) ht₀
  have huniq : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-k) →
      ∃! r, r ∈ X.image (fun s => s + t₀) ∧ Valued.v (x - r) ≤ WithZero.exp (-m) := by
    intro x hx
    have hxt : Valued.v (x - t₀) ≤ WithZero.exp (-k) := (Valuation.map_sub _ _ _).trans (max_le hx ht₀)
    obtain ⟨r, ⟨hrX, hr⟩, hr_uniq⟩ := hX' (x - t₀) hxt
    refine ⟨r + t₀, ⟨Finset.mem_image.2 ⟨r, hrX, rfl⟩, ?_⟩, ?_⟩
    · rw [sub_add_eq_sub_sub_swap]
      exact hr
    · rintro s ⟨hs, hxs⟩
      obtain ⟨r', hr'X, hr's⟩ := Finset.mem_image.1 hs
      have hxs' : Valued.v (x - t₀ - r') ≤ WithZero.exp (-m) := by
        rw [← sub_add_eq_sub_sub_swap, hr's]
        exact hxs
      rw [← hr's, hr_uniq r' ⟨hr'X, hxs'⟩]
  have hterm : ∀ r ∈ X, χ (-r) • gl3AmbientRightTranslate (R := ℂ) (u r) (gl3AmbientRightTranslate (R := ℂ) (u t₀) g)
      = χ t₀ • (χ (-(r + t₀)) • gl3AmbientRightTranslate (R := ℂ) (u (r + t₀)) g) := by
    intro r _
    have h : (-r : v.adicCompletion ℚ) = t₀ + -(r + t₀) := by ring
    rw [← translate_mul, ← hu, smul_smul, ← AddChar.map_add_eq_mul, ← h]
  have himg : ∑ s ∈ X.image (fun s => s + t₀), χ (-s) • gl3AmbientRightTranslate (R := ℂ) (u s) g
      = ∑ r ∈ X, χ (-(r + t₀)) • gl3AmbientRightTranslate (R := ℂ) (u (r + t₀)) g :=
    Finset.sum_image fun a _ b _ h => add_right_cancel h
  rw [rootAverage_apply, rootAverage_apply, Finset.sum_congr rfl hterm, ← Finset.smul_sum, ← himg]
  congr 1
  exact sum_eq_sum_of_reps v hconst hmem huniq hX hX'

private theorem card_smul_sub_rootAverage_mem (u : v.adicCompletion ℚ → LocalGL3 v)
    (χ : AddChar (v.adicCompletion ℚ) ℂ) (X : Finset (v.adicCompletion ℚ)) {S : Submodule ℂ (LocalGL3 v → ℂ)}
    {f : LocalGL3 v → ℂ} (hf : f ∈ S) :
    (X.card : ℂ) • f - rootAverage v u χ X f ∈ coinvKer v u χ S := by
  have hcard : (X.card : ℂ) • f = ∑ _r ∈ X, f := by
    rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  rw [rootAverage_apply, hcard, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun r _ => ?_
  show f - χ (-r) • gl3AmbientRightTranslate (R := ℂ) (u r) f ∈ coinvKer v u χ S
  have h1 : χ (-r) * χ r = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hr : f - χ (-r) • gl3AmbientRightTranslate (R := ℂ) (u r) f =
      (-χ (-r)) • (gl3AmbientRightTranslate (R := ℂ) (u r) f - χ r • f) := by
    rw [smul_sub, smul_smul, neg_mul, h1, neg_smul, neg_smul, one_smul, sub_neg_eq_add, neg_add_eq_sub]
  rw [hr]
  exact Submodule.smul_mem _ _ (sub_mem_coinvKer v u χ hf r)

private theorem isKilled_of_mem_coinvKer {u : v.adicCompletion ℚ → LocalGL3 v} (hu : ∀ a b, u (a + b) = u a * u b)
    {χ : AddChar (v.adicCompletion ℚ) ℂ}
    (hχ : ∃ mχ : ℤ, ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-mχ) → χ t = 1)
    {S : Submodule ℂ (LocalGL3 v → ℂ)}
    (hS : ∀ f ∈ S, ∃ mf : ℤ, ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-mf) →
      gl3AmbientRightTranslate (R := ℂ) (u t) f = f)
    {d : LocalGL3 v → ℂ} (hd : d ∈ coinvKer v u χ S) : IsKilled v u χ d := by
  obtain ⟨mχ, hmχ⟩ := hχ
  refine Submodule.span_induction (p := fun d _ => IsKilled v u χ d) ?_ ?_ ?_ ?_ hd
  · rintro _ ⟨t₀, f, hf, rfl⟩
    obtain ⟨n, hn⟩ := exists_valued_le_exp v t₀
    obtain ⟨mf, hmf⟩ := hS f hf
    refine ⟨-(n : ℤ), max mf mχ, fun k m hk hm X hX hX' => ?_⟩
    have ht₀ : Valued.v t₀ ≤ WithZero.exp (-k) := hn.trans (WithZero.exp_le_exp.mpr (by omega))
    have hg : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-m) →
        gl3AmbientRightTranslate (R := ℂ) (u t) f = f :=
      fun t ht => hmf t (ht.trans (WithZero.exp_le_exp.mpr (by omega)))
    have hχ' : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-m) → χ t = 1 :=
      fun t ht => hmχ t (ht.trans (WithZero.exp_le_exp.mpr (by omega)))
    rw [map_sub, map_smul, rootAverage_translate v hu χ hX hX' ht₀ hg hχ', sub_self]
  · exact ⟨0, 0, fun _ _ _ _ _ _ _ => map_zero _⟩
  · rintro d₁ d₂ - - ⟨k₁, m₁, h₁⟩ ⟨k₂, m₂, h₂⟩
    refine ⟨min k₁ k₂, max m₁ m₂, fun k m hk hm X hX hX' => ?_⟩
    rw [map_add, h₁ k m (by omega) (by omega) X hX hX', h₂ k m (by omega) (by omega) X hX hX', add_zero]
  · rintro c d - ⟨k₁, m₁, h₁⟩
    refine ⟨k₁, m₁, fun k m hk hm X hX hX' => ?_⟩
    rw [map_smul, h₁ k m hk hm X hX hX', smul_zero]

private theorem exists_card_ne_zero_rootAverage_eq_zero {u : v.adicCompletion ℚ → LocalGL3 v}
    {χ : AddChar (v.adicCompletion ℚ) ℂ} {d : LocalGL3 v → ℂ} (hd : IsKilled v u χ d) :
    ∃ X : Finset (v.adicCompletion ℚ), (X.card : ℂ) ≠ 0 ∧ rootAverage v u χ X d = 0 := by
  obtain ⟨k₀, m₀, h⟩ := hd
  obtain ⟨X, hX, hX', hcard⟩ := exists_finset_ball_representatives v (min k₀ m₀) (max k₀ m₀) (by omega)
  refine ⟨X, ?_, h (min k₀ m₀) (max k₀ m₀) (min_le_left _ _) (le_max_right _ _) X hX hX'⟩
  rw [hcard, Nat.cast_pow]
  exact pow_ne_zero _ (natCast_natCard_quot_ne_zero v)

private theorem translate_rootAverage {u : v.adicCompletion ℚ → LocalGL3 v} (χ : AddChar (v.adicCompletion ℚ) ℂ)
    (X : Finset (v.adicCompletion ℚ)) {g : LocalGL3 v} (hg : ∀ t, g * u t = u t * g) (f : LocalGL3 v → ℂ) :
    gl3AmbientRightTranslate (R := ℂ) g (rootAverage v u χ X f) =
      rootAverage v u χ X (gl3AmbientRightTranslate (R := ℂ) g f) := by
  rw [rootAverage_apply, rootAverage_apply, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_smul, ← translate_mul, ← translate_mul, hg]

private theorem rootAverage_mem_coinvKer {u u' : v.adicCompletion ℚ → LocalGL3 v}
    (huu' : ∀ s t, u' s * u t = u t * u' s) (χ χ' : AddChar (v.adicCompletion ℚ) ℂ) (X : Finset (v.adicCompletion ℚ))
    {S : Submodule ℂ (LocalGL3 v → ℂ)}
    (hS : ∀ (g : LocalGL3 v) (f : LocalGL3 v → ℂ), f ∈ S → gl3AmbientRightTranslate (R := ℂ) g f ∈ S)
    {d : LocalGL3 v → ℂ} (hd : d ∈ coinvKer v u' χ' S) : rootAverage v u χ X d ∈ coinvKer v u' χ' S := by
  refine Submodule.span_induction (p := fun d _ => rootAverage v u χ X d ∈ coinvKer v u' χ' S) ?_ ?_ ?_ ?_ hd
  · rintro _ ⟨s, f, hf, rfl⟩
    rw [map_sub, map_smul, ← translate_rootAverage v χ X (huu' s)]
    exact sub_mem_coinvKer v u' χ' (rootAverage_mem v hS X hf) s
  · simp only [map_zero, Submodule.zero_mem]
  · intro d₁ d₂ _ _ h₁ h₂
    simpa only [map_add] using Submodule.add_mem _ h₁ h₂
  · intro c d _ h
    simpa only [map_smul] using Submodule.smul_mem _ c h

private theorem rootAverage_rootY_mem_sup (ψ : AddChar (v.adicCompletion ℚ) ℂ) (X : Finset (v.adicCompletion ℚ))
    {S : Submodule ℂ (LocalGL3 v → ℂ)}
    (hS : ∀ (g : LocalGL3 v) (f : LocalGL3 v → ℂ), f ∈ S → gl3AmbientRightTranslate (R := ℂ) g f ∈ S)
    {d : LocalGL3 v → ℂ} (hd : d ∈ coinvKer v (rootX v) ψ S) :
    rootAverage v (rootY v) ψ X d ∈ coinvKer v (rootX v) ψ S ⊔ coinvKer v (rootZ v) 1 S := by
  refine Submodule.span_induction
    (p := fun d _ => rootAverage v (rootY v) ψ X d ∈ coinvKer v (rootX v) ψ S ⊔ coinvKer v (rootZ v) 1 S)
    ?_ ?_ ?_ ?_ hd
  · rintro _ ⟨a, f, hf, rfl⟩
    rw [map_sub, map_smul, rootAverage_apply, rootAverage_apply, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun r _ => ?_
    have hf₁ : gl3AmbientRightTranslate (R := ℂ) (rootY v r) f ∈ S := hS _ _ hf
    have hC := sub_mem_coinvKer v (rootZ v) 1 hf (-(a * r))
    rw [AddChar.one_apply, one_smul] at hC
    have hcomm : gl3AmbientRightTranslate (R := ℂ) (rootY v r) (gl3AmbientRightTranslate (R := ℂ) (rootX v a) f) =
        gl3AmbientRightTranslate (R := ℂ) (rootX v a) (gl3AmbientRightTranslate (R := ℂ) (rootY v r)
          (gl3AmbientRightTranslate (R := ℂ) (rootZ v (-(a * r))) f)) := by
      rw [← translate_mul, rootY_mul_rootX, translate_mul, translate_mul]
    have key :
        ψ (-r) • gl3AmbientRightTranslate (R := ℂ) (rootY v r) (gl3AmbientRightTranslate (R := ℂ) (rootX v a) f) -
          ψ a • (ψ (-r) • gl3AmbientRightTranslate (R := ℂ) (rootY v r) f) =
        ψ (-r) • (gl3AmbientRightTranslate (R := ℂ) (rootX v a) (gl3AmbientRightTranslate (R := ℂ) (rootY v r) f) -
            ψ a • gl3AmbientRightTranslate (R := ℂ) (rootY v r) f) +
          ψ (-r) • gl3AmbientRightTranslate (R := ℂ) (rootX v a) (gl3AmbientRightTranslate (R := ℂ) (rootY v r)
            (gl3AmbientRightTranslate (R := ℂ) (rootZ v (-(a * r))) f - f)) := by
      rw [hcomm, map_sub, map_sub]
      module
    rw [key]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.smul_mem _ _ (sub_mem_coinvKer v (rootX v) ψ hf₁ a)))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (translate_mem_coinvKer v hS (fun t => rootX_mul_rootZ v a t)
        (translate_mem_coinvKer v hS (fun t => rootY_mul_rootZ v r t) hC))))
  · simp only [map_zero, Submodule.zero_mem]
  · intro d₁ d₂ _ _ h₁ h₂
    simpa only [map_add] using Submodule.add_mem _ h₁ h₂
  · intro c d _ h
    simpa only [map_smul] using Submodule.smul_mem _ c h

private theorem apply_eq_zero_of_mem_coinvKerN (ψ : AddChar (v.adicCompletion ℚ) ℂ) (W : LocalGL3 v → ℂ)
    {L : ↥(gl3CyclicSubspace W) →ₗ[ℂ] ℂ} (hL : L ∈ gl3WhittakerFunctionalSpace (gl3CyclicRep W) ψ)
    (f : ↥(gl3CyclicSubspace W)) (hf : (f : LocalGL3 v → ℂ) ∈ coinvKerN v ψ (gl3CyclicSubspace W)) : L f = 0 := by
  have hL' : IsGL3WhittakerFunctional (gl3CyclicRep W) ψ L := hL
  have hle : coinvKerN v ψ (gl3CyclicSubspace W) ≤ (LinearMap.ker L).map (gl3CyclicSubspace W).subtype := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, y, z, u, hu, rfl⟩
    refine ⟨gl3CyclicRep W (upperUnipotent3 x y z) ⟨u, hu⟩ - ψ (x + y) • ⟨u, hu⟩, ?_, rfl⟩
    show gl3CyclicRep W (upperUnipotent3 x y z) ⟨u, hu⟩ - ψ (x + y) • ⟨u, hu⟩ ∈ LinearMap.ker L
    rw [LinearMap.mem_ker, map_sub, map_smul, hL' x y z ⟨u, hu⟩, smul_eq_mul, sub_self]
  obtain ⟨k, hk, hkf⟩ := hle hf
  have hkf' : k = f := Subtype.ext hkf
  rw [← hkf']
  exact hk

private theorem mem_gl3WhittakerFunctionalSpace_of_forall (ψ : AddChar (v.adicCompletion ℚ) ℂ) (W : LocalGL3 v → ℂ)
    {L : ↥(gl3CyclicSubspace W) →ₗ[ℂ] ℂ}
    (hL : ∀ f : ↥(gl3CyclicSubspace W), (f : LocalGL3 v → ℂ) ∈ coinvKerN v ψ (gl3CyclicSubspace W) → L f = 0) :
    L ∈ gl3WhittakerFunctionalSpace (gl3CyclicRep W) ψ := by
  show IsGL3WhittakerFunctional (gl3CyclicRep W) ψ L
  intro x y z f
  have h := hL (gl3CyclicRep W (upperUnipotent3 x y z) f - ψ (x + y) • f) (sub_mem_coinvKerN v ψ f.2 x y z)
  rwa [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h

private noncomputable def restrictFunctional (ψ : AddChar (v.adicCompletion ℚ) ℂ) {W W' : LocalGL3 v → ℂ}
    (h : gl3CyclicSubspace W' ≤ gl3CyclicSubspace W) :
    ↥(gl3WhittakerFunctionalSpace (gl3CyclicRep W) ψ) →ₗ[ℂ] ↥(gl3WhittakerFunctionalSpace (gl3CyclicRep W') ψ) where
  toFun L := ⟨L.1.comp (Submodule.inclusion h), by
    intro x y z f
    show L.1 (Submodule.inclusion h (gl3CyclicRep W' (upperUnipotent3 x y z) f)) =
      ψ (x + y) * L.1 (Submodule.inclusion h f)
    rw [show Submodule.inclusion h (gl3CyclicRep W' (upperUnipotent3 x y z) f) =
      gl3CyclicRep W (upperUnipotent3 x y z) (Submodule.inclusion h f) from Subtype.ext rfl]
    exact L.2 x y z _⟩
  map_add' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)

private theorem mem_sup_coinvKer_of_mem_sup {u : v.adicCompletion ℚ → LocalGL3 v} (hu : ∀ a b, u (a + b) = u a * u b)
    {χ : AddChar (v.adicCompletion ℚ) ℂ}
    (hχ : ∃ mχ : ℤ, ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-mχ) → χ t = 1)
    {S S' P Q : Submodule ℂ (LocalGL3 v → ℂ)}
    (hsmS : ∀ f ∈ S, ∃ mf : ℤ, ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-mf) →
      gl3AmbientRightTranslate (R := ℂ) (u t) f = f)
    (hPQ : ∀ X : Finset (v.adicCompletion ℚ), ∀ p ∈ P, rootAverage v u χ X p ∈ Q)
    {f : LocalGL3 v → ℂ} (hfS' : f ∈ S') (hf : f ∈ P ⊔ coinvKer v u χ S) : f ∈ Q ⊔ coinvKer v u χ S' := by
  obtain ⟨p, hp, d, hd, rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨X, hX0, hXd⟩ := exists_card_ne_zero_rootAverage_eq_zero v (isKilled_of_mem_coinvKer v hu hχ hsmS hd)
  have hB := card_smul_sub_rootAverage_mem v u χ X hfS'
  have hsum : (X.card : ℂ) • (p + d) =
      ((X.card : ℂ) • (p + d) - rootAverage v u χ X (p + d)) + rootAverage v u χ X p := by
    rw [map_add, hXd, add_zero, sub_add_cancel]
  rw [← Submodule.smul_mem_iff _ hX0, hsum]
  exact Submodule.add_mem _ (Submodule.mem_sup_right hB) (Submodule.mem_sup_left (hPQ X p hp))

private theorem mem_coinvKerN_of_mem_coinvKerN {ψ : AddChar (v.adicCompletion ℚ) ℂ}
    (hψ : ∃ mψ : ℤ, ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-mψ) → ψ t = 1)
    {S S' : Submodule ℂ (LocalGL3 v → ℂ)}
    (hS : ∀ (g : LocalGL3 v) (f : LocalGL3 v → ℂ), f ∈ S → gl3AmbientRightTranslate (R := ℂ) g f ∈ S)
    (hS' : ∀ (g : LocalGL3 v) (f : LocalGL3 v → ℂ), f ∈ S' → gl3AmbientRightTranslate (R := ℂ) g f ∈ S')
    (hsm : ∀ f ∈ S, ∃ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) ∧
      ∀ k ∈ U, gl3AmbientRightTranslate (R := ℂ) k f = f)
    {f : LocalGL3 v → ℂ} (hfS' : f ∈ S') (hf : f ∈ coinvKerN v ψ S) : f ∈ coinvKerN v ψ S' := by

  have hsmX : ∀ f ∈ S, ∃ mf : ℤ, ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-mf) →
      gl3AmbientRightTranslate (R := ℂ) (rootX v t) f = f := fun f hf => by
    obtain ⟨U, hUo, hUf⟩ := hsm f hf
    exact exists_forall_translate_eq_of_continuous v (continuous_rootX v) (rootX_zero v) hUo hUf
  have hsmY : ∀ f ∈ S, ∃ mf : ℤ, ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-mf) →
      gl3AmbientRightTranslate (R := ℂ) (rootY v t) f = f := fun f hf => by
    obtain ⟨U, hUo, hUf⟩ := hsm f hf
    exact exists_forall_translate_eq_of_continuous v (continuous_rootY v) (rootY_zero v) hUo hUf
  have hsmZ : ∀ f ∈ S, ∃ mf : ℤ, ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-mf) →
      gl3AmbientRightTranslate (R := ℂ) (rootZ v t) f = f := fun f hf => by
    obtain ⟨U, hUo, hUf⟩ := hsm f hf
    exact exists_forall_translate_eq_of_continuous v (continuous_rootZ v) (rootZ_zero v) hUo hUf
  have h1 : ∃ m₁ : ℤ, ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-m₁) →
      (1 : AddChar (v.adicCompletion ℚ) ℂ) t = 1 := ⟨0, fun t _ => AddChar.one_apply t⟩

  have hleX : coinvKer v (rootX v) ψ S' ≤ S' := coinvKer_le v hS'
  have hleY : coinvKer v (rootY v) ψ S' ≤ S' := coinvKer_le v hS'
  have hleZ : coinvKer v (rootZ v) 1 S' ≤ S' := coinvKer_le v hS'

  have hf₀ : f ∈ (coinvKer v (rootX v) ψ S ⊔ coinvKer v (rootY v) ψ S) ⊔ coinvKer v (rootZ v) 1 S :=
    coinvKerN_le_sup v hS hf
  have hf₁ : f ∈ (coinvKer v (rootX v) ψ S ⊔ coinvKer v (rootY v) ψ S) ⊔ coinvKer v (rootZ v) 1 S' :=
    mem_sup_coinvKer_of_mem_sup v (rootZ_add v) h1 hsmZ (fun X p hp => by
      obtain ⟨pX, hpX, pY, hpY, rfl⟩ := Submodule.mem_sup.mp hp
      rw [map_add]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (rootAverage_mem_coinvKer v (fun s t => rootX_mul_rootZ v s t) 1 ψ X hS hpX))
        (Submodule.mem_sup_right (rootAverage_mem_coinvKer v (fun s t => rootY_mul_rootZ v s t) 1 ψ X hS hpY)))
      hfS' hf₀
  obtain ⟨g₁, hg₁, e₁, he₁, rfl⟩ := Submodule.mem_sup.mp hf₁
  have hg₁S' : g₁ ∈ S' := by
    rw [← add_sub_cancel_right g₁ e₁]
    exact S'.sub_mem hfS' (hleZ he₁)

  have hg₁' : g₁ ∈ (coinvKer v (rootX v) ψ S ⊔ coinvKer v (rootZ v) 1 S) ⊔ coinvKer v (rootY v) ψ S' :=
    mem_sup_coinvKer_of_mem_sup v (rootY_add v) hψ hsmY
      (fun X p hp => rootAverage_rootY_mem_sup v ψ X hS hp) hg₁S' hg₁
  obtain ⟨g₂, hg₂, e₂, he₂, rfl⟩ := Submodule.mem_sup.mp hg₁'
  have hg₂S' : g₂ ∈ S' := by
    rw [← add_sub_cancel_right g₂ e₂]
    exact S'.sub_mem hg₁S' (hleY he₂)

  have hg₂' : g₂ ∈ coinvKer v (rootX v) ψ S ⊔ coinvKer v (rootZ v) 1 S' :=
    mem_sup_coinvKer_of_mem_sup v (rootZ_add v) h1 hsmZ
      (fun X p hp => rootAverage_mem_coinvKer v (fun s t => rootX_mul_rootZ v s t) 1 ψ X hS hp) hg₂S' hg₂
  obtain ⟨g₃, hg₃, e₃, he₃, rfl⟩ := Submodule.mem_sup.mp hg₂'
  have hg₃S' : g₃ ∈ S' := by
    rw [← add_sub_cancel_right g₃ e₃]
    exact S'.sub_mem hg₂S' (hleZ he₃)

  have hg₃' : g₃ ∈ (⊥ : Submodule ℂ (LocalGL3 v → ℂ)) ⊔ coinvKer v (rootX v) ψ S' :=
    mem_sup_coinvKer_of_mem_sup v (rootX_add v) hψ hsmX (fun X p hp => by
      rw [(Submodule.mem_bot ℂ).mp hp, map_zero]
      exact Submodule.zero_mem _) hg₃S'
      (Submodule.mem_sup_right hg₃ : g₃ ∈ (⊥ : Submodule ℂ (LocalGL3 v → ℂ)) ⊔ coinvKer v (rootX v) ψ S)
  rw [bot_sup_eq] at hg₃'

  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (coinvKer_rootX_le v ψ S' hg₃')
    (coinvKer_rootZ_le v ψ S' he₃)) (coinvKer_rootY_le v ψ S' he₂)) (coinvKer_rootZ_le v ψ S' he₁)

end LanglandsTunnell.CubicInduction.TwistedCoinvariantAverage

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_hasWhittakerMultOne_of_mem_gl3CyclicSubspace_of_isOpen.LanglandsTunnell.CubicInduction"

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψv : Continuous ψv)
    (W : LocalGL3 v → ℂ)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hmo : HasWhittakerMultOne ψv W)
    (W' : LocalGL3 v → ℂ) (hW' : W' ∈ gl3CyclicSubspace W) :
    HasWhittakerMultOne ψv W' := by
  have _ := hψv
  unfold HasWhittakerMultOne GL3WhittakerUniquenessStatement at hmo ⊢
  have hle : gl3CyclicSubspace W' ≤ gl3CyclicSubspace W :=
    Submodule.span_le.mpr (by
      rintro _ ⟨h, rfl⟩
      exact gl3AmbientRightTranslate_mem_gl3CyclicSubspace W h hW')
  have hstab : ∀ (g : LocalGL3 v) (f : LocalGL3 v → ℂ), f ∈ gl3CyclicSubspace W →
      gl3AmbientRightTranslate (R := ℂ) g f ∈ gl3CyclicSubspace W :=
    fun g f hf => gl3AmbientRightTranslate_mem_gl3CyclicSubspace W g hf
  have hstab' : ∀ (g : LocalGL3 v) (f : LocalGL3 v → ℂ), f ∈ gl3CyclicSubspace W' →
      gl3AmbientRightTranslate (R := ℂ) g f ∈ gl3CyclicSubspace W' :=
    fun g f hf => gl3AmbientRightTranslate_mem_gl3CyclicSubspace W' g hf
  by_cases hA : ∃ m : ℤ, ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-m) → ψv t = 1
  ·
    refine (LinearMap.rank_le_of_surjective (TwistedCoinvariantAverage.restrictFunctional v ψv hle) ?_).trans hmo
    intro L'
    let KV : Submodule ℂ ↥(gl3CyclicSubspace W) :=
      (TwistedCoinvariantAverage.coinvKerN v ψv (gl3CyclicSubspace W)).comap (gl3CyclicSubspace W).subtype
    let m : ↥(gl3CyclicSubspace W') →ₗ[ℂ] ↥(gl3CyclicSubspace W) ⧸ KV := KV.mkQ.comp (Submodule.inclusion hle)
    have hker : LinearMap.ker m ≤ LinearMap.ker L'.1 := by
      intro f hf
      rw [LinearMap.mem_ker] at hf ⊢
      have hf0 : Submodule.Quotient.mk (p := KV) (Submodule.inclusion hle f) = 0 := hf
      have hf' : ((Submodule.inclusion hle f : ↥(gl3CyclicSubspace W)) : LocalGL3 v → ℂ) ∈
          TwistedCoinvariantAverage.coinvKerN v ψv (gl3CyclicSubspace W) :=
        (Submodule.Quotient.mk_eq_zero KV).mp hf0
      exact TwistedCoinvariantAverage.apply_eq_zero_of_mem_coinvKerN v ψv W' L'.2 f
        (TwistedCoinvariantAverage.mem_coinvKerN_of_mem_coinvKerN v hA hstab hstab'
          (fun f hf => TwistedCoinvariantAverage.exists_isOpen_forall_translate_eq v hsm hf) f.2 hf')
    let ℓ₀ : ↥(LinearMap.range m) →ₗ[ℂ] ℂ :=
      ((LinearMap.ker m).liftQ L'.1 hker).comp m.quotKerEquivRange.symm.toLinearMap
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
    have hL : ℓ.comp KV.mkQ ∈ gl3WhittakerFunctionalSpace (gl3CyclicRep W) ψv :=
      TwistedCoinvariantAverage.mem_gl3WhittakerFunctionalSpace_of_forall v ψv W fun f hf => by
        show ℓ (KV.mkQ f) = 0
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero KV).mpr hf, map_zero]
    refine ⟨⟨ℓ.comp KV.mkQ, hL⟩, Subtype.ext (LinearMap.ext fun f => ?_)⟩
    show ℓ (KV.mkQ (Submodule.inclusion hle f)) = L'.1 f
    have h1 : ℓ (m f) = ℓ₀ ⟨m f, LinearMap.mem_range_self m f⟩ :=
      LinearMap.congr_fun hℓ ⟨m f, LinearMap.mem_range_self m f⟩
    rw [show KV.mkQ (Submodule.inclusion hle f) = m f from rfl, h1]
    show (LinearMap.ker m).liftQ L'.1 hker (m.quotKerEquivRange.symm ⟨m f, LinearMap.mem_range_self m f⟩) = L'.1 f
    rw [LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  ·
    have hzero : ∀ L : ↥(gl3WhittakerFunctionalSpace (gl3CyclicRep W') ψv), L = 0 := by
      intro L
      refine Subtype.ext (LinearMap.ext fun f => ?_)
      show L.1 f = 0
      obtain ⟨U, hUo, hUf⟩ := TwistedCoinvariantAverage.exists_isOpen_forall_translate_eq v hsm (hle f.2)
      obtain ⟨m, hm⟩ := TwistedCoinvariantAverage.exists_forall_translate_eq_of_continuous v
        (TwistedCoinvariantAverage.continuous_rootX v) (TwistedCoinvariantAverage.rootX_zero v) hUo hUf
      obtain ⟨t, ht, hψt⟩ : ∃ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (-m) ∧ ψv t ≠ 1 := by
        by_contra h
        exact hA ⟨m, fun t ht => by_contra fun h' => h ⟨t, ht, h'⟩⟩
      have h1 : L.1 (gl3CyclicRep W' (upperUnipotent3 t 0 0) f) = ψv (t + 0) * L.1 f := L.2 t 0 0 f
      have h2 : gl3CyclicRep W' (upperUnipotent3 t 0 0) f = f := Subtype.ext (hm t ht)
      rw [h2, add_zero] at h1
      have h3 : (ψv t - 1) * L.1 f = 0 := by rw [sub_mul, one_mul, ← h1, sub_self]
      exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hψt)
    haveI : Subsingleton ↥(gl3WhittakerFunctionalSpace (gl3CyclicRep W') ψv) :=
      ⟨fun a b => (hzero a).trans (hzero b).symm⟩
    rw [rank_subsingleton']
    exact zero_le_one

end S_LanglandsTunnell_CubicInduction_hasWhittakerMultOne_of_mem_gl3CyclicSubspace_of_isOpen
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_hasWhittakerMultOne_of_mem_gl3CyclicSubspace_of_isOpen (solution)
