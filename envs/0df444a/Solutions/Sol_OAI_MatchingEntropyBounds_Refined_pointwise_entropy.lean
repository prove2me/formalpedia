-- Prove2me | solution 1 for OAI.MatchingEntropyBounds.Refined.pointwise_entropy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T13:12:37.248988+00:00
-- url     : https://prove2.me/submissions/1c586f8e-63b7-4ffb-8dbe-20617cc07416

import Mathlib
import Definitions.Def_MatchingEntropyBounds

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434

universe uV uE uIndex uι uI uJ uA uB uC uW uF uD

namespace LooplessGraph
end LooplessGraph

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE}
  [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

end LooplessGraph

namespace LooplessGraph

end LooplessGraph

namespace Refined

end Refined

end MatchingEntropyBounds

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators


namespace MatchingEntropyBounds

theorem probabilitySimplex_eq_range (Index : Type uIndex) [Fintype Index] :
    probabilitySimplex Index = stdSimplex ℝ Index := rfl

theorem convex_probabilitySimplex (Index : Type uIndex) [Fintype Index] :
    Convex ℝ (probabilitySimplex Index) := by
  intro leftWeights leftMem rightWeights rightMem leftScale rightScale
    leftNonneg rightNonneg total
  constructor
  · intro index
    exact add_nonneg (mul_nonneg leftNonneg (leftMem.1 index))
      (mul_nonneg rightNonneg (rightMem.1 index))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, leftMem.2, rightMem.2, mul_one, total]

theorem single_mem_probabilitySimplex {Index : Type uIndex} [Fintype Index]
    [DecidableEq Index] (index : Index) : Pi.single index 1 ∈ probabilitySimplex Index := by
  constructor
  · intro other
    simp only [Pi.single_apply]
    split <;> norm_num
  · simp

theorem mem_Icc_of_mem_probabilitySimplex {Index : Type uIndex} [Fintype Index]
    {weights : Index → ℝ} (mem : weights ∈ probabilitySimplex Index) (index : Index) :
    weights index ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨mem.1 index, ?_⟩
  rw [← mem.2]
  exact Finset.single_le_sum (fun other _ ↦ mem.1 other) (Finset.mem_univ index)

theorem isCompact_probabilitySimplex (Index : Type uIndex) [Fintype Index] :
    IsCompact (probabilitySimplex Index) := by
  rw [probabilitySimplex_eq_range]
  exact isCompact_stdSimplex ℝ Index

end MatchingEntropyBounds

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds

section PolyhedralPrelude
variable {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]

def finitePolyhedron (L : I → (J → ℝ) →ₗ[ℝ] ℝ) (b : I → ℝ) : Set (J → ℝ) :=
  {x | ∀ i, L i x ≤ b i}

theorem finitePolyhedron_eventually_line (L : I → (J → ℝ) →ₗ[ℝ] ℝ) (b : I → ℝ)
    {x : J → ℝ} (hx : x ∈ finitePolyhedron L b) (u : J → ℝ)
    (hu : ∀ i, L i x = b i → L i u = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, x+t • u ∈ finitePolyhedron L b := by
  apply Filter.eventually_all.mpr
  intro i
  by_cases hi : L i x=b i
  · apply Filter.Eventually.of_forall
    intro t
    rw [map_add, map_smul, hu i hi, smul_zero, add_zero, hi]
  · have hlt : L i x < b i := lt_of_le_of_ne (hx i) hi
    have hc : Continuous (fun t : ℝ => L i (x+t • u)) :=
      (L i).continuous_of_finiteDimensional.comp (by fun_prop)
    have hh : ∀ᶠ t : ℝ in 𝓝 0, L i (x+t • u) < b i :=
      (isOpen_lt hc continuous_const).mem_nhds (by simpa using hlt : L i (x+(0:ℝ) • u) < b i)
    exact hh.mono fun t ht => le_of_lt ht

theorem finitePolyhedron_eventually_expand (L : I → (J → ℝ) →ₗ[ℝ] ℝ) (b : I → ℝ)
    {x : J → ℝ} (hx : x ∈ finitePolyhedron L b) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ y in 𝓝[finitePolyhedron L b] x, x+t⁻¹ • (y-x) ∈ finitePolyhedron L b := by
  apply Filter.eventually_all.mpr
  intro i
  by_cases hi : L i x=b i
  · filter_upwards [eventually_mem_nhdsWithin] with y hy
    rw [map_add, map_smul, map_sub, hi]
    change b i+t⁻¹ * (L i y-b i) ≤ b i
    have hh := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le) (sub_nonpos.mpr (hy i))
    linarith
  · have hlt : L i x < b i := lt_of_le_of_ne (hx i) hi
    have hc : Continuous (fun y : J → ℝ => L i (x+t⁻¹ • (y-x))) :=
      (L i).continuous_of_finiteDimensional.comp (by fun_prop)
    have hh : ∀ᶠ y : J → ℝ in 𝓝 x, L i (x+t⁻¹ • (y-x)) < b i :=
      (isOpen_lt hc continuous_const).mem_nhds (by simpa using hlt : L i (x+t⁻¹ • (x-x)) < b i)
    exact (hh.filter_mono nhdsWithin_le_nhds).mono fun y hy => le_of_lt hy

omit [Fintype J] in
theorem extreme_point_direction_zero (P : Set (J → ℝ)) {x : J → ℝ}
    (hx : x ∈ Set.extremePoints ℝ P) (u : J → ℝ)
    (hu : ∀ᶠ t : ℝ in 𝓝 0, x+t • u ∈ P) : u=0 := by
  have hu' : ∀ᶠ t : ℝ in 𝓝 0, x+(-t) • u ∈ P := by
    have hc : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by simpa using (continuous_neg.tendsto (0:ℝ))
    exact hc.eventually hu

  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0, (x+t • u ∈ P ∧ x+(-t) • u ∈ P) ∧ 0<t :=
    ((hu.and hu').filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  obtain ⟨a,⟨ha,hna⟩,ha0⟩ := hh.exists
  have hseg : x ∈ openSegment ℝ (x+a • u) (x+(-a) • u) := by
    refine ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have he := (mem_extremePoints.mp hx).2 _ ha _ hna hseg |>.1
  ext j
  have hj := congrFun he j
  change x j+a*u j=x j at hj
  change u j=0
  exact (mul_eq_zero.mp (by linarith : a*u j=0)).resolve_left (ne_of_gt ha0)

section LinearHelper
open Module
variable {A : Type uA} {B : Type uB} {C : Type uC} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module ℝ A] [Module ℝ B] [Module ℝ C]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]

theorem quotient_finrank_le_of_ker_le (U : Submodule ℝ A) (f : A →ₗ[ℝ] B)
    (h : f.ker ≤ U) : finrank ℝ (A ⧸ U) ≤ finrank ℝ B := by
  have h1 := U.finrank_quotient_add_finrank
  have h2 := f.finrank_range_add_finrank_ker
  have h3 := Submodule.finrank_mono h
  have h4 : finrank ℝ f.range ≤ finrank ℝ B := Submodule.finrank_le _
  omega

theorem quotient_finrank_le_pair (U : Submodule ℝ A) (W : Submodule ℝ B) (Z : Submodule ℝ C)
    (f : A →ₗ[ℝ] B) (g : A →ₗ[ℝ] C)
    (h : ∀ u, f u ∈ W → g u ∈ Z → u ∈ U) :
    finrank ℝ (A ⧸ U) ≤ finrank ℝ (B ⧸ W)+finrank ℝ (C ⧸ Z) := by
  let F := (W.mkQ.comp f).prod (Z.mkQ.comp g)
  have hk : F.ker ≤ U := by
    intro u hu
    have hh : (W.mkQ (f u), Z.mkQ (g u))=0 := hu
    have hW : f u ∈ W := by
      have hq := congrArg Prod.fst hh
      simpa using hq
    have hZ : g u ∈ Z := by
      have hq := congrArg Prod.snd hh
      simpa using hq
    exact h u hW hZ
  simpa using quotient_finrank_le_of_ker_le U F hk

end LinearHelper
end PolyhedralPrelude

end MatchingEntropyBounds

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def fiberMass {A : Type uA} {C : Type uC} [Fintype A] [DecidableEq C]
    (p : A → ℝ) (f : A → C) (c : C) : ℝ := ∑ a, if f a = c then p a else 0

theorem fiberMass_nonneg {A : Type uA} {C : Type uC} [Fintype A] [DecidableEq C]
    {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (f : A → C) (c : C) :
    0 ≤ fiberMass p f c := by
  apply Finset.sum_nonneg
  intro a _
  split <;> simp_all

theorem le_fiberMass_self {A : Type uA} {C : Type uC} [Fintype A] [DecidableEq C]
    {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (f : A → C) (a : A) :
    p a ≤ fiberMass p f (f a) := by
  have h := Finset.single_le_sum (s := Finset.univ) (a := a)
    (f := fun b => if f b = f a then p b else 0)
    (by intro b _; split <;> simp_all) (Finset.mem_univ a)
  simpa only [fiberMass, ite_true] using h

def jointLaw {A : Type uA} {B : Type uB} {C : Type uC} [Fintype A] [Fintype B] [DecidableEq C]
    (p : A → ℝ) (q : B → ℝ) (f : A → C) (g : B → C) (z : A × B) : ℝ :=
  if f z.1 = g z.2 then p z.1*q z.2 / fiberMass p f (f z.1) else 0

theorem jointLaw_nonneg {A : Type uA} {B : Type uB} {C : Type uC} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b)
    (f : A → C) (g : B → C) (z : A × B) : 0 ≤ jointLaw p q f g z := by
  unfold jointLaw
  split
  · exact div_nonneg (mul_nonneg (hp _) (hq _)) (fiberMass_nonneg hp f _)
  · rfl

theorem jointLaw_first {A : Type uA} {B : Type uB} {C : Type uC} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : ∀ a, 0 ≤ p a)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (a : A) : (∑ b, jointLaw p q f g (a,b)) = p a := by
  have heq : ∀ b, jointLaw p q f g (a,b) =
      (p a / fiberMass p f (f a)) * (if g b=f a then q b else 0) := by
    intro b
    by_cases h : f a=g b
    · simp only [jointLaw, h, ite_true]
      ring
    · simp [jointLaw, h, Ne.symm h]
  simp_rw [heq]
  rw [← Finset.mul_sum]
  change p a / fiberMass p f (f a) * fiberMass q g (f a) = p a
  rw [← hcompat]
  by_cases hz : fiberMass p f (f a) = 0
  · have ha : p a = 0 := le_antisymm (by simpa [hz] using le_fiberMass_self hp f a) (hp a)
    simp [ha]
  · exact div_mul_cancel₀ _ hz

theorem jointLaw_second {A : Type uA} {B : Type uB} {C : Type uC} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hq : ∀ b, 0 ≤ q b)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (b : B) : (∑ a, jointLaw p q f g (a,b)) = q b := by
  have heq : ∀ a, jointLaw p q f g (a,b) =
      (q b / fiberMass q g (g b)) * (if f a=g b then p a else 0) := by
    intro a
    by_cases h : f a=g b
    · simp only [jointLaw, h, ite_true, ← hcompat]
      ring
    · simp [jointLaw, h]
  simp_rw [heq]
  rw [← Finset.mul_sum]
  change q b / fiberMass q g (g b) * fiberMass p f (g b) = q b
  rw [hcompat]
  by_cases hz : fiberMass q g (g b) = 0
  · have hb : q b = 0 := le_antisymm (by simpa [hz] using le_fiberMass_self hq g b) (hq b)
    simp [hb]
  · exact div_mul_cancel₀ _ hz

theorem jointLaw_mem_simplex {A : Type uA} {B : Type uB} {C : Type uC} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : p ∈ probabilitySimplex A) (hq : q ∈ probabilitySimplex B)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c) :
    jointLaw p q f g ∈ probabilitySimplex (A × B) := by
  refine ⟨jointLaw_nonneg hp.1 hq.1 f g, ?_⟩
  rw [Fintype.sum_prod_type]
  simp_rw [jointLaw_first hp.1 f g hcompat]
  exact hp.2

theorem sum_subtype_supported {A : Type uA} [Fintype A] (P : A → Prop) [DecidablePred P]
    (w : A → ℝ) (hsupp : ∀ a, ¬P a → w a = 0) :
    (∑ a : {a // P a}, w a.val) = ∑ a, w a := by
  have hh : (∑ a : {a // ¬P a}, w a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact hsupp a.val a.property
  simpa only [hh, add_zero] using (Fintype.sum_subtype_add_sum_subtype P w)

theorem compatible_jointLaw_mem_simplex {A : Type uA} {B : Type uB} {C : Type uC} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : p ∈ probabilitySimplex A) (hq : q ∈ probabilitySimplex B)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c) :
    (fun z : {z : A × B // f z.1=g z.2} => jointLaw p q f g z.val) ∈
      probabilitySimplex {z : A × B // f z.1=g z.2} := by
  refine ⟨fun z => jointLaw_nonneg hp.1 hq.1 f g z.val, ?_⟩
  rw [sum_subtype_supported (fun z : A × B => f z.1=g z.2) (jointLaw p q f g)
    (by intro z hz; simp [jointLaw, hz])]
  exact (jointLaw_mem_simplex hp hq f g hcompat).2

theorem fiberMass_sum {A : Type uA} {C : Type uC} [Fintype A] [Fintype C] [DecidableEq C]
    (p : A → ℝ) (f : A → C) : ∑ c, fiberMass p f c = ∑ a, p a := by
  unfold fiberMass
  rw [Finset.sum_comm]
  simp

theorem fiberMass_expect {A : Type uA} {C : Type uC} [Fintype A] [Fintype C] [DecidableEq C]
    (p : A → ℝ) (f : A → C) (h : C → ℝ) :
    ∑ c, fiberMass p f c * h c = ∑ a, p a*h (f a) := by
  unfold fiberMass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  simp

theorem fiberMass_mem_simplex {A : Type uA} {C : Type uC} [Fintype A] [Fintype C] [DecidableEq C]
    {p : A → ℝ} (hp : p ∈ probabilitySimplex A) (f : A → C) :
    fiberMass p f ∈ probabilitySimplex C :=
  ⟨fiberMass_nonneg hp.1 f, (fiberMass_sum p f).trans hp.2⟩

theorem jointLaw_expect_first {A : Type uA} {B : Type uB} {C : Type uC} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : ∀ a, 0 ≤ p a)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (h : A → ℝ) : ∑ z : A × B, jointLaw p q f g z * h z.1 = ∑ a, p a*h a := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul, jointLaw_first hp f g hcompat]

theorem jointLaw_expect_second {A : Type uA} {B : Type uB} {C : Type uC} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hq : ∀ b, 0 ≤ q b)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (h : B → ℝ) : ∑ z : A × B, jointLaw p q f g z * h z.2 = ∑ b, q b*h b := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, jointLaw_second hq f g hcompat]

theorem compatible_jointLaw_expect_first {A : Type uA} {B : Type uB} {C : Type uC} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hp : ∀ a, 0 ≤ p a)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (h : A → ℝ) :
    ∑ z : {z : A × B // f z.1=g z.2}, jointLaw p q f g z.val * h z.val.1 = ∑ a, p a*h a := by
  rw [sum_subtype_supported (fun z : A × B => f z.1=g z.2)
    (fun z => jointLaw p q f g z * h z.1)
    (by intro z hz; simp [jointLaw, hz])]
  exact jointLaw_expect_first hp f g hcompat h

theorem compatible_jointLaw_expect_second {A : Type uA} {B : Type uB} {C : Type uC} [Fintype A] [Fintype B] [DecidableEq C]
    {p : A → ℝ} {q : B → ℝ} (hq : ∀ b, 0 ≤ q b)
    (f : A → C) (g : B → C) (hcompat : ∀ c, fiberMass p f c = fiberMass q g c)
    (h : B → ℝ) :
    ∑ z : {z : A × B // f z.1=g z.2}, jointLaw p q f g z.val * h z.val.2 = ∑ b, q b*h b := by
  rw [sum_subtype_supported (fun z : A × B => f z.1=g z.2)
    (fun z => jointLaw p q f g z * h z.2)
    (by intro z hz; simp [jointLaw, hz])]
  exact jointLaw_expect_second hq f g hcompat h

end MatchingEntropyBounds

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds.LooplessGraph

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq V] in
@[simp] theorem indicator_nonneg (G : LooplessGraph V E) (M : G.Matching) (e : E) :
    0 ≤ G.indicator M e := by
  simp only [indicator]
  split <;> norm_num

omit [Fintype V] [Fintype E] [DecidableEq V] in
@[simp] theorem indicator_le_one (G : LooplessGraph V E) (M : G.Matching) (e : E) :
    G.indicator M e ≤ 1 := by
  simp only [indicator]
  split <;> norm_num

omit [Fintype V] [DecidableEq V] in
theorem continuous_mean (G : LooplessGraph V E) : Continuous G.mean := by
  unfold mean
  fun_prop

def meanLinear (G : LooplessGraph V E) : (G.Matching → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun := G.mean
  map_add' p q := by
    ext e
    simp [mean, add_mul, Finset.sum_add_distrib]
  map_smul' a p := by
    ext e
    simp [mean, mul_assoc, Finset.mul_sum]

omit [Fintype V] [DecidableEq V] in
theorem mean_mem_polytope (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) : G.mean p ∈ G.polytope := by
  have h := (convex_convexHull ℝ (Set.range G.indicator)).sum_mem
    (fun M _ ↦ hp.1 M) hp.2 (fun M _ ↦ subset_convexHull ℝ _ (Set.mem_range_self M))
  have he : G.mean p = ∑ M, p M • G.indicator M := by
    ext e
    simp [mean]
  rw [he]
  exact h

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mean_single (G : LooplessGraph V E) (M : G.Matching) :
    G.mean (Pi.single M 1) = G.indicator M := by
  classical
  ext e
  simp [mean, Pi.single_apply, ite_mul]

omit [Fintype V] [DecidableEq V] in

theorem mem_polytope_iff (G : LooplessGraph V E) (y : E → ℝ) :
    y ∈ G.polytope ↔ (G.feasibleLaws y).Nonempty := by
  classical
  constructor
  · intro hy
    have hc : Convex ℝ (G.mean '' probabilitySimplex G.Matching) :=
      (convex_probabilitySimplex G.Matching).linear_image G.meanLinear
    have hs : Set.range G.indicator ⊆ G.mean '' probabilitySimplex G.Matching := by
      rintro _ ⟨M, rfl⟩
      exact ⟨Pi.single M 1, single_mem_probabilitySimplex M, G.mean_single M⟩
    obtain ⟨p, hp, rfl⟩ := convexHull_min hs hc hy
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact G.mean_mem_polytope hp

omit [Fintype V] [DecidableEq V] in
theorem compact_feasibleLaws (G : LooplessGraph V E) (y : E → ℝ) :
    IsCompact (G.feasibleLaws y) := by
  exact (isCompact_probabilitySimplex G.Matching).inter_right
    (isClosed_eq G.continuous_mean continuous_const)

omit [Fintype V] [DecidableEq V] in
theorem compact_polytope (G : LooplessGraph V E) : IsCompact G.polytope := by
  have heq : G.polytope = G.mean '' probabilitySimplex G.Matching := by
    ext y
    rw [G.mem_polytope_iff]
    rfl
  rw [heq]
  exact (isCompact_probabilitySimplex G.Matching).image G.continuous_mean

end MatchingEntropyBounds.LooplessGraph

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds.LooplessGraph

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def Crosses (G : LooplessGraph V E) (S : Finset V) (e : E) : Prop :=
  (G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.left e ∉ S ∧ G.right e ∈ S)

instance crossesDecidable (G : LooplessGraph V E) (S : Finset V) (e : E) :
    Decidable (G.Crosses S e) := inferInstanceAs (Decidable
      ((G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.left e ∉ S ∧ G.right e ∈ S)))

def cut (G : LooplessGraph V E) (S : Finset V) : Finset E :=
  Finset.univ.filter (G.Crosses S)

def degree (G : LooplessGraph V E) (x : E → ℝ) (v : V) : ℝ :=
  ∑ e, if G.Incident v e then x e else 0

def cutMass (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ G.cut S, x e

def constraintPolytope (G : LooplessGraph V E) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ v, G.degree x v = 1) ∧
    (∀ S : Finset V, Odd S.card → 1 ≤ G.cutMass x S)}

omit [Fintype V] [DecidableEq E] in
@[simp] theorem mem_cut (G : LooplessGraph V E) (S : Finset V) (e : E) :
    e ∈ G.cut S ↔ G.Crosses S e := by simp [cut]

omit [Fintype E] [DecidableEq E] in
theorem crosses_compl (G : LooplessGraph V E) (S : Finset V) (e : E) :
    G.Crosses Sᶜ e ↔ G.Crosses S e := by
  simp only [Crosses, Finset.mem_compl, not_not]
  tauto

omit [DecidableEq E] in
@[simp] theorem cut_compl (G : LooplessGraph V E) (S : Finset V) :
    G.cut Sᶜ = G.cut S := by ext; simp [crosses_compl]

omit [Fintype V] in
theorem degree_indicator (G : LooplessGraph V E) (M : G.Matching) (v : V) :
    G.degree (G.indicator M) v = 1 := by
  obtain ⟨e, ⟨he, hev⟩, huniq⟩ := M.property v
  rw [degree, Finset.sum_eq_single e]
  · simp [hev, indicator, he]
  · intro e' _ hne
    by_cases hv : G.Incident v e'
    · have hh : e' ∉ M.val := by
        intro hm
        exact hne (huniq e' ⟨hm, hv⟩)
      simp [hv, indicator, hh]
    · simp [hv]
  · simp

omit [Fintype V] in
theorem degree_mean (G : LooplessGraph V E) (p : G.Matching → ℝ) (v : V) :
    G.degree (G.mean p) v = ∑ M, p M := by
  classical
  have he : ∀ e, (if G.Incident v e then G.mean p e else 0) =
      ∑ M, p M*(if G.Incident v e then G.indicator M e else 0) := by
    intro e
    by_cases h : G.Incident v e <;> simp [h, mean]
  unfold degree
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  rw [← Finset.mul_sum]
  change p M*G.degree (G.indicator M) v = p M
  rw [G.degree_indicator, mul_one]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem incidence_sum (G : LooplessGraph V E) (e : E) (S : Finset V) :
    (∑ v ∈ S, if G.Incident v e then (1:ℕ) else 0) =
      (if G.left e ∈ S then 1 else 0) + (if G.right e ∈ S then 1 else 0) := by
  have hv : ∀ v, (if G.Incident v e then (1:ℕ) else 0) =
      (if v = G.left e then 1 else 0) + (if v = G.right e then 1 else 0) := by
    intro v
    by_cases hl : v = G.left e <;> by_cases hr : v = G.right e
    · exact ((G.loopless e) (hl.symm.trans hr)).elim
    · simp [Incident, hl, G.loopless e, Ne.symm (G.loopless e)]
    · simp [Incident, hr, G.loopless e, Ne.symm (G.loopless e)]
    · simp [Incident, Ne.symm hl, Ne.symm hr, hl, hr]
  simp_rw [hv, Finset.sum_add_distrib]
  simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem matching_incidence_count (G : LooplessGraph V E) (M : G.Matching)
    (S : Finset V) :
    (∑ e ∈ M.val, ((if G.left e ∈ S then (1:ℕ) else 0) +
      (if G.right e ∈ S then 1 else 0))) = S.card := by
  have hsum : ∀ v, (∑ e ∈ M.val, if G.Incident v e then (1:ℕ) else 0) = 1 := by
    intro v
    obtain ⟨e, ⟨he, hev⟩, hu⟩ := M.property v
    rw [Finset.sum_eq_single e]
    · simp [hev]
    · intro e' he' hh
      have hv : ¬G.Incident v e' := fun hv => hh (hu e' ⟨he', hv⟩)
      simp [hv]
    · simp [he]
  calc
    _ = ∑ e ∈ M.val, ∑ v ∈ S, if G.Incident v e then (1:ℕ) else 0 := by
      simp_rw [incidence_sum]
    _ = ∑ v ∈ S, ∑ e ∈ M.val, if G.Incident v e then (1:ℕ) else 0 := Finset.sum_comm
    _ = S.card := by simp_rw [hsum]; simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem matching_crosses_odd (G : LooplessGraph V E) (M : G.Matching)
    (S : Finset V) (hS : Odd S.card) : ∃ e ∈ M.val, G.Crosses S e := by
  by_contra h
  push Not at h
  have heq : ∀ e ∈ M.val, ((if G.left e ∈ S then (1:ℕ) else 0) +
      (if G.right e ∈ S then 1 else 0)) = 2*(if G.left e ∈ S then 1 else 0) := by
    intro e he
    have hc := h e he
    simp only [Crosses] at hc
    by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S <;>
      simp_all
  have hh := G.matching_incidence_count M S
  have heqsum := Finset.sum_congr rfl heq
  rw [heqsum, ← Finset.mul_sum] at hh
  obtain ⟨k, hk⟩ := hS
  omega

omit [Fintype V] [DecidableEq E] in
theorem degree_linear (G : LooplessGraph V E) (x y : E → ℝ) (a b : ℝ) (v : V) :
    G.degree (a • x+b • y) v = a*G.degree x v+b*G.degree y v := by
  have he : ∀ e, (if G.Incident v e then (a • x+b • y) e else 0) =
      a*(if G.Incident v e then x e else 0)+b*(if G.Incident v e then y e else 0) := by
    intro e
    by_cases h : G.Incident v e <;> simp [h]
  simp only [degree, he, Finset.sum_add_distrib, ← Finset.mul_sum]

omit [Fintype V] [DecidableEq E] in
theorem cutMass_linear (G : LooplessGraph V E) (x y : E → ℝ) (a b : ℝ) (S : Finset V) :
    G.cutMass (a • x+b • y) S = a*G.cutMass x S+b*G.cutMass y S := by
  simp [cutMass, Finset.sum_add_distrib, Finset.mul_sum]

omit [Fintype V] [DecidableEq E] in
theorem convex_constraintPolytope (G : LooplessGraph V E) :
    Convex ℝ G.constraintPolytope := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun e => add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e)), ?_, ?_⟩
  · intro v
    rw [degree_linear, hx.2.1, hy.2.1, mul_one, mul_one, hab]
  · intro S hS
    rw [cutMass_linear]
    calc
      1 = a*1+b*1 := by linarith
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hx.2.2 S hS) ha)
        (mul_le_mul_of_nonneg_left (hy.2.2 S hS) hb)

omit [Fintype V] in
theorem indicator_mem_constraintPolytope (G : LooplessGraph V E) (M : G.Matching) :
    G.indicator M ∈ G.constraintPolytope := by
  refine ⟨?_, G.degree_indicator M, ?_⟩
  · intro e; simp [indicator]; split <;> norm_num
  · intro S hS
    obtain ⟨e, he, hc⟩ := G.matching_crosses_odd M S hS
    have h := Finset.single_le_sum (f := G.indicator M)
      (s := G.cut S) (a := e) (by intro e' _; simp [indicator]; split <;> norm_num)
      ((G.mem_cut S e).mpr hc)
    simpa only [cutMass, indicator, he, ite_true] using h

omit [Fintype V] in
theorem polytope_subset_constraintPolytope (G : LooplessGraph V E) :
    G.polytope ⊆ G.constraintPolytope := by
  apply convexHull_min
  · rintro x ⟨M, rfl⟩
    exact G.indicator_mem_constraintPolytope M
  · exact G.convex_constraintPolytope

omit [Fintype V] [DecidableEq E] in
theorem constraint_coordinate_le_one (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) (e : E) : x e ≤ 1 := by
  have h := Finset.single_le_sum (f := fun e' => if G.Incident (G.left e) e' then x e' else 0)
    (s := Finset.univ) (a := e) (by
      intro e' _; split; exact hx.1 e'; rfl) (Finset.mem_univ e)
  have he : G.Incident (G.left e) e := Or.inl rfl
  change (if G.Incident (G.left e) e then x e else 0) ≤ G.degree x (G.left e) at h
  simpa only [he, ite_true, hx.2.1] using h

omit [Fintype V] [DecidableEq E] in
theorem continuous_degree (G : LooplessGraph V E) (v : V) :
    Continuous (fun x : E → ℝ => G.degree x v) := by
  unfold degree
  apply continuous_finsetSum
  intro e _
  split <;> fun_prop

omit [Fintype V] [DecidableEq E] in
theorem continuous_cutMass (G : LooplessGraph V E) (S : Finset V) :
    Continuous (fun x : E → ℝ => G.cutMass x S) := by
  unfold cutMass
  fun_prop

omit [Fintype V] [DecidableEq E] in
theorem isClosed_constraintPolytope (G : LooplessGraph V E) :
    IsClosed G.constraintPolytope := by
  simp only [constraintPolytope, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter fun e => isClosed_le continuous_const (continuous_apply e)).inter
    ((isClosed_iInter fun v => isClosed_eq (G.continuous_degree v) continuous_const).inter
      (isClosed_iInter fun S => isClosed_iInter fun _ =>
        isClosed_le continuous_const (G.continuous_cutMass S)))

omit [Fintype V] [DecidableEq E] in
theorem isCompact_constraintPolytope (G : LooplessGraph V E) :
    IsCompact G.constraintPolytope := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : E → ℝ) 1)).of_isClosed_subset
    G.isClosed_constraintPolytope
  intro x hx
  exact ⟨hx.1, fun e => G.constraint_coordinate_le_one hx e⟩

end MatchingEntropyBounds.LooplessGraph

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds.LooplessGraph

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def onSide (G : LooplessGraph V E) (S : Finset V) :
    LooplessGraph (Option {v // v ∈ S}) {e // G.left e ∈ S ∨ G.right e ∈ S} where
  left e := if h : G.left e.val ∈ S then some ⟨G.left e.val, h⟩ else none
  right e := if h : G.right e.val ∈ S then some ⟨G.right e.val, h⟩ else none
  loopless e := by
    dsimp
    split_ifs with hl hr
    · intro he
      have hv := Option.some.inj he
      exact G.loopless e.val (congrArg Subtype.val hv)
    · simp
    · simp
    · rename_i hr
      exact (e.property.elim hl hr).elim

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem onSide_incident_some (G : LooplessGraph V E) (S : Finset V)
    (v : {v // v ∈ S}) (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    (G.onSide S).Incident (some v) e ↔ G.Incident v.val e.val := by
  have hf : ∀ (w : V),
      (if h : w ∈ S then some (⟨w,h⟩ : {v // v ∈ S}) else none) = some v ↔ w=v.val := by
    intro w
    by_cases hw : w ∈ S
    · simp only [hw, ↓reduceDIte, Option.some.injEq]
      exact Subtype.ext_iff
    · simp only [hw, ↓reduceDIte]
      constructor
      · intro h
        cases h
      · intro he
        exact (hw (he.symm ▸ v.property)).elim
  change ((if h : G.left e.val ∈ S then some ⟨G.left e.val,h⟩ else none) = some v ∨
    (if h : G.right e.val ∈ S then some ⟨G.right e.val,h⟩ else none) = some v) ↔ _
  rw [hf, hf]
  rfl

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem onSide_incident_none (G : LooplessGraph V E) (S : Finset V)
    (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    (G.onSide S).Incident none e ↔ G.Crosses S e.val := by
  simp only [Incident, onSide, Crosses]
  by_cases hl : G.left e.val ∈ S <;> by_cases hr : G.right e.val ∈ S <;>
    simp [hl, hr]
  exact (e.property.elim hl hr).elim

def boundaryEdge (G : LooplessGraph V E) (S : Finset V) (M : (G.onSide S).Matching) :
    {e // G.left e ∈ S ∨ G.right e ∈ S} := Classical.choose (M.property none)

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem boundaryEdge_mem (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) : G.boundaryEdge S M ∈ M.val :=
  (Classical.choose_spec (M.property none)).1.1

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem boundaryEdge_crosses (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) : G.Crosses S (G.boundaryEdge S M).val :=
  (G.onSide_incident_none S _).mp (Classical.choose_spec (M.property none)).1.2

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem eq_boundaryEdge (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) {e : {e // G.left e ∈ S ∨ G.right e ∈ S}}
    (he : e ∈ M.val) (hc : G.Crosses S e.val) : e = G.boundaryEdge S M :=
  (Classical.choose_spec (M.property none)).2 e ⟨he, (G.onSide_incident_none S e).mpr hc⟩

def liftedEdges (G : LooplessGraph V E) (S : Finset V) (M : (G.onSide S).Matching) : Finset E :=
  M.val.image Subtype.val

omit [Fintype V] [Fintype E] in
theorem mem_liftedEdges (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    e.val ∈ G.liftedEdges S M ↔ e ∈ M.val := by
  simp only [liftedEdges, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, he⟩
    have he' : a = e := Subtype.ext he
    simpa only [he'] using ha
  · intro he
    exact ⟨e, he, rfl⟩

omit [Fintype V] [Fintype E] in
theorem liftedEdges_keep (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) {e : E} (he : e ∈ G.liftedEdges S M) :
    G.left e ∈ S ∨ G.right e ∈ S := by
  rcases Finset.mem_image.mp he with ⟨a, _, rfl⟩
  exact a.property

omit [Fintype V] [Fintype E] in
theorem lifted_cross_eq_boundary (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) {e : E} (he : e ∈ G.liftedEdges S M)
    (hc : G.Crosses S e) : e = (G.boundaryEdge S M).val := by
  let e' : {e // G.left e ∈ S ∨ G.right e ∈ S} := ⟨e, G.liftedEdges_keep S M he⟩
  exact congrArg Subtype.val (G.eq_boundaryEdge S M ((G.mem_liftedEdges S M e').mp he) hc)

omit [Fintype V] [Fintype E] in
theorem boundary_mem_lifted (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) : (G.boundaryEdge S M).val ∈ G.liftedEdges S M :=
  (G.mem_liftedEdges S M _).mpr (G.boundaryEdge_mem S M)

omit [Fintype E] [DecidableEq E] in
theorem crosses_of_kept_both (G : LooplessGraph V E) (S : Finset V) (e : E)
    (h₁ : G.left e ∈ S ∨ G.right e ∈ S)
    (h₂ : G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ) : G.Crosses S e := by
  simp only [Finset.mem_compl] at h₂
  unfold Crosses
  tauto

omit [Fintype E] in

theorem lifted_other_subset (G : LooplessGraph V E) (S : Finset V)
    (M₁ : (G.onSide S).Matching) (M₂ : (G.onSide Sᶜ).Matching)
    (heq : (G.boundaryEdge S M₁).val = (G.boundaryEdge Sᶜ M₂).val)
    {e : E} (he : e ∈ G.liftedEdges Sᶜ M₂)
    (hkeep : G.left e ∈ S ∨ G.right e ∈ S) : e ∈ G.liftedEdges S M₁ := by
  have hc := G.crosses_of_kept_both S e hkeep (G.liftedEdges_keep Sᶜ M₂ he)
  have hcb : G.Crosses Sᶜ e := (G.crosses_compl S e).mpr hc
  rw [G.lifted_cross_eq_boundary Sᶜ M₂ he hcb, ← heq]
  exact G.boundary_mem_lifted S M₁

omit [Fintype E] in

theorem mem_glued_left (G : LooplessGraph V E) (S : Finset V)
    (M₁ : (G.onSide S).Matching) (M₂ : (G.onSide Sᶜ).Matching)
    (heq : (G.boundaryEdge S M₁).val = (G.boundaryEdge Sᶜ M₂).val)
    (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    e.val ∈ G.liftedEdges S M₁ ∪ G.liftedEdges Sᶜ M₂ ↔ e ∈ M₁.val := by
  simp only [Finset.mem_union]
  constructor
  · rintro (h | h)
    · exact (G.mem_liftedEdges S M₁ e).mp h
    · exact (G.mem_liftedEdges S M₁ e).mp (G.lifted_other_subset S M₁ M₂ heq h e.property)
  · intro h
    exact Or.inl ((G.mem_liftedEdges S M₁ e).mpr h)

omit [Fintype E] in
theorem mem_glued_right (G : LooplessGraph V E) (S : Finset V)
    (M₁ : (G.onSide S).Matching) (M₂ : (G.onSide Sᶜ).Matching)
    (heq : (G.boundaryEdge S M₁).val = (G.boundaryEdge Sᶜ M₂).val)
    (e : {e // G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ}) :
    e.val ∈ G.liftedEdges S M₁ ∪ G.liftedEdges Sᶜ M₂ ↔ e ∈ M₂.val := by
  simp only [Finset.mem_union]
  constructor
  · rintro (h | h)
    · have hc := G.crosses_of_kept_both S e.val (G.liftedEdges_keep S M₁ h) e.property
      have he := (G.lifted_cross_eq_boundary S M₁ h hc).trans heq
      apply (G.mem_liftedEdges Sᶜ M₂ e).mp
      rw [he]
      exact G.boundary_mem_lifted Sᶜ M₂
    · exact (G.mem_liftedEdges Sᶜ M₂ e).mp h
  · intro h
    exact Or.inr ((G.mem_liftedEdges Sᶜ M₂ e).mpr h)

omit [Fintype E] in
theorem glued_perfect (G : LooplessGraph V E) (S : Finset V)
    (M₁ : (G.onSide S).Matching) (M₂ : (G.onSide Sᶜ).Matching)
    (heq : (G.boundaryEdge S M₁).val = (G.boundaryEdge Sᶜ M₂).val) :
    G.IsPerfectMatching (G.liftedEdges S M₁ ∪ G.liftedEdges Sᶜ M₂) := by
  intro v
  by_cases hv : v ∈ S
  · obtain ⟨e, ⟨he, hev⟩, hu⟩ := M₁.property (some ⟨v,hv⟩)
    have hev' := (G.onSide_incident_some S ⟨v,hv⟩ e).mp hev
    refine ⟨e.val, ⟨(G.mem_glued_left S M₁ M₂ heq e).mpr he, hev'⟩, ?_⟩
    rintro f ⟨hf, hfv⟩
    have hk : G.left f ∈ S ∨ G.right f ∈ S := by
      rcases hfv with h | h
      · exact Or.inl (h.symm ▸ hv)
      · exact Or.inr (h.symm ▸ hv)
    let f' : {e // G.left e ∈ S ∨ G.right e ∈ S} := ⟨f,hk⟩
    have hf' : f' ∈ M₁.val := (G.mem_glued_left S M₁ M₂ heq f').mp hf
    exact congrArg Subtype.val (hu f' ⟨hf', (G.onSide_incident_some S ⟨v,hv⟩ f').mpr hfv⟩)
  · have hv' := Finset.mem_compl.mpr hv
    obtain ⟨e, ⟨he, hev⟩, hu⟩ := M₂.property (some ⟨v,hv'⟩)
    have hev' := (G.onSide_incident_some Sᶜ ⟨v,hv'⟩ e).mp hev
    refine ⟨e.val, ⟨(G.mem_glued_right S M₁ M₂ heq e).mpr he, hev'⟩, ?_⟩
    rintro f ⟨hf, hfv⟩
    have hk : G.left f ∈ Sᶜ ∨ G.right f ∈ Sᶜ := by
      rcases hfv with h | h
      · exact Or.inl (h.symm ▸ hv')
      · exact Or.inr (h.symm ▸ hv')
    let f' : {e // G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ} := ⟨f,hk⟩
    have hf' : f' ∈ M₂.val := (G.mem_glued_right S M₁ M₂ heq f').mp hf
    exact congrArg Subtype.val (hu f' ⟨hf', (G.onSide_incident_some Sᶜ ⟨v,hv'⟩ f').mpr hfv⟩)

def glueMatching (G : LooplessGraph V E) (S : Finset V)
    (z : {z : (G.onSide S).Matching × (G.onSide Sᶜ).Matching //
      (G.boundaryEdge S z.1).val = (G.boundaryEdge Sᶜ z.2).val}) : G.Matching :=
  ⟨G.liftedEdges S z.val.1 ∪ G.liftedEdges Sᶜ z.val.2,
    G.glued_perfect S z.val.1 z.val.2 z.property⟩

omit [Fintype E] in
theorem indicator_glue_left (G : LooplessGraph V E) (S : Finset V)
    (z : {z : (G.onSide S).Matching × (G.onSide Sᶜ).Matching //
      (G.boundaryEdge S z.1).val = (G.boundaryEdge Sᶜ z.2).val})
    (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    G.indicator (G.glueMatching S z) e.val = (G.onSide S).indicator z.val.1 e := by
  simp only [indicator, glueMatching, G.mem_glued_left S z.val.1 z.val.2 z.property e]

omit [Fintype E] in
theorem indicator_glue_right (G : LooplessGraph V E) (S : Finset V)
    (z : {z : (G.onSide S).Matching × (G.onSide Sᶜ).Matching //
      (G.boundaryEdge S z.1).val = (G.boundaryEdge Sᶜ z.2).val})
    (e : {e // G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ}) :
    G.indicator (G.glueMatching S z) e.val = (G.onSide Sᶜ).indicator z.val.2 e := by
  simp only [indicator, glueMatching, G.mem_glued_right S z.val.1 z.val.2 z.property e]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem boundary_eq_iff_mem (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) (e : {e // G.left e ∈ S ∨ G.right e ∈ S})
    (hc : G.Crosses S e.val) : (G.boundaryEdge S M).val=e.val ↔ e ∈ M.val := by
  constructor
  · intro h
    have he : G.boundaryEdge S M = e := Subtype.ext h
    exact he ▸ G.boundaryEdge_mem S M
  · intro h
    exact (congrArg Subtype.val (G.eq_boundaryEdge S M h hc)).symm

omit [Fintype V] in
theorem boundary_fiber (G : LooplessGraph V E) (S : Finset V)
    (p : (G.onSide S).Matching → ℝ) (e : {e // G.left e ∈ S ∨ G.right e ∈ S})
    (hc : G.Crosses S e.val) :
    fiberMass p (fun M => (G.boundaryEdge S M).val) e.val = (G.onSide S).mean p e := by
  unfold fiberMass mean
  apply Finset.sum_congr rfl
  intro M _
  simp only [G.boundary_eq_iff_mem S M e hc, indicator]
  split <;> simp

omit [Fintype V] in
theorem boundary_fiber_zero (G : LooplessGraph V E) (S : Finset V)
    (p : (G.onSide S).Matching → ℝ) (e : E) (hc : ¬G.Crosses S e) :
    fiberMass p (fun M => (G.boundaryEdge S M).val) e = 0 := by
  apply Finset.sum_eq_zero
  intro M _
  have he : (G.boundaryEdge S M).val ≠ e := by
    intro h
    exact hc (h ▸ G.boundaryEdge_crosses S M)
  simp [he]

theorem couple_laws (G : LooplessGraph V E) (S : Finset V) (x : E → ℝ)
    {p : (G.onSide S).Matching → ℝ} {q : (G.onSide Sᶜ).Matching → ℝ}
    (hp : p ∈ probabilitySimplex (G.onSide S).Matching)
    (hq : q ∈ probabilitySimplex (G.onSide Sᶜ).Matching)
    (hpx : ∀ e, (G.onSide S).mean p e = x e.val)
    (hqx : ∀ e, (G.onSide Sᶜ).mean q e = x e.val) :
    ∃ r, r ∈ G.feasibleLaws x := by
  let f := fun M : (G.onSide S).Matching => (G.boundaryEdge S M).val
  let g := fun M : (G.onSide Sᶜ).Matching => (G.boundaryEdge Sᶜ M).val
  have hc : ∀ e, fiberMass p f e = fiberMass q g e := by
    intro e
    by_cases he : G.Crosses S e
    · have hk : G.left e ∈ S ∨ G.right e ∈ S := he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
      have he' := (G.crosses_compl S e).mpr he
      have hk' : G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ := he'.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
      rw [G.boundary_fiber S p ⟨e,hk⟩ he, G.boundary_fiber Sᶜ q ⟨e,hk'⟩ he', hpx, hqx]
    · have he' : ¬G.Crosses Sᶜ e := fun h => he ((G.crosses_compl S e).mp h)
      rw [G.boundary_fiber_zero S p e he, G.boundary_fiber_zero Sᶜ q e he']
  let Z := {z : (G.onSide S).Matching × (G.onSide Sᶜ).Matching // f z.1=g z.2}
  let w : Z → ℝ := fun z => jointLaw p q f g z.val
  have hw : w ∈ probabilitySimplex Z := compatible_jointLaw_mem_simplex hp hq f g hc
  refine ⟨fiberMass w (G.glueMatching S), fiberMass_mem_simplex hw _, ?_⟩
  ext e
  rw [mean, fiberMass_expect]
  by_cases he : G.left e ∈ S ∨ G.right e ∈ S
  · have hi : ∀ z : Z, G.indicator (G.glueMatching S z) e =
        (G.onSide S).indicator z.val.1 ⟨e,he⟩ := fun z => G.indicator_glue_left S z ⟨e,he⟩
    simp_rw [hi]
    exact (compatible_jointLaw_expect_first hp.1 f g hc
      (fun M => (G.onSide S).indicator M ⟨e,he⟩)).trans (hpx ⟨e,he⟩)
  · have he' : G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ := by
      simp only [not_or] at he
      exact Or.inl (Finset.mem_compl.mpr he.1)
    have hi : ∀ z : Z, G.indicator (G.glueMatching S z) e =
        (G.onSide Sᶜ).indicator z.val.2 ⟨e,he'⟩ := fun z => G.indicator_glue_right S z ⟨e,he'⟩
    simp_rw [hi]
    exact (compatible_jointLaw_expect_second hq.1 f g hc
      (fun M => (G.onSide Sᶜ).indicator M ⟨e,he'⟩)).trans (hqx ⟨e,he'⟩)

def sideMap (S : Finset V) (v : V) : Option {v // v ∈ S} :=
  if h : v ∈ S then some ⟨v,h⟩ else none

def liftVertices (S : Finset V) (T : Finset (Option {v // v ∈ S})) : Finset V :=
  Finset.univ.filter (fun v => sideMap S v ∈ T)

@[simp] theorem mem_liftVertices (S : Finset V)
    (T : Finset (Option {v // v ∈ S})) (v : V) :
    v ∈ liftVertices S T ↔ sideMap S v ∈ T := by simp [liftVertices]

omit [Fintype V] in
@[simp] theorem sideMap_some (S : Finset V) (v : {v // v ∈ S}) :
    sideMap S v.val = some v := by
  simp [sideMap, v.property]

theorem liftVertices_card (S : Finset V) (T : Finset (Option {v // v ∈ S}))
    (hn : none ∉ T) : (liftVertices S T).card = T.card := by
  apply Finset.card_bij (fun v _ => sideMap S v)
  · intro v hv
    exact (mem_liftVertices S T v).mp hv
  · intro v hv w hw he
    have hvS : v ∈ S := by
      by_contra h
      have hmem := (mem_liftVertices S T v).mp hv
      simp only [sideMap, h, ↓reduceDIte] at hmem
      exact hn hmem
    have hwS : w ∈ S := by
      by_contra h
      have hmem := (mem_liftVertices S T w).mp hw
      simp only [sideMap, h, ↓reduceDIte] at hmem
      exact hn hmem
    simp only [sideMap, hvS, hwS, ↓reduceDIte, Option.some.injEq] at he
    exact congrArg Subtype.val he
  · intro t ht
    cases t with
    | none => exact (hn ht).elim
    | some v => exact ⟨v.val, by simpa only [mem_liftVertices, sideMap_some] using ht, sideMap_some S v⟩

omit [Fintype E] [DecidableEq E] in
theorem onSide_cut_crosses (G : LooplessGraph V E) (S : Finset V)
    (T : Finset (Option {v // v ∈ S})) (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    (G.onSide S).Crosses T e ↔ G.Crosses (liftVertices S T) e.val := by
  simp only [Crosses, mem_liftVertices]
  rfl

omit [Fintype E] [DecidableEq E] in
theorem crosses_lift_kept (G : LooplessGraph V E) (S : Finset V)
    (T : Finset (Option {v // v ∈ S})) (e : E)
    (he : G.Crosses (liftVertices S T) e) : G.left e ∈ S ∨ G.right e ∈ S := by
  by_contra h
  simp only [not_or] at h
  simp only [Crosses, mem_liftVertices, sideMap, h.1, h.2, ↓reduceDIte] at he
  tauto

omit [DecidableEq E] in
theorem onSide_cutMass (G : LooplessGraph V E) (S : Finset V)
    (x : E → ℝ) (T : Finset (Option {v // v ∈ S})) :
    (G.onSide S).cutMass (fun e => x e.val) T = G.cutMass x (liftVertices S T) := by
  simp only [cutMass, cut, Finset.sum_filter]
  simp_rw [G.onSide_cut_crosses S T]
  exact sum_subtype_supported (fun e => G.left e ∈ S ∨ G.right e ∈ S)
    (fun e => if G.Crosses (liftVertices S T) e then x e else 0)
    (by intro e he; rw [ite_eq_right (fun hc => he (G.crosses_lift_kept S T e hc))])

omit [Fintype V] [DecidableEq E] in
theorem onSide_degree_some (G : LooplessGraph V E) (S : Finset V)
    (x : E → ℝ) (v : {v // v ∈ S}) :
    (G.onSide S).degree (fun e => x e.val) (some v) = G.degree x v.val := by
  simp only [degree]
  simp_rw [G.onSide_incident_some S v]
  apply sum_subtype_supported (fun e => G.left e ∈ S ∨ G.right e ∈ S)
    (fun e => if G.Incident v.val e then x e else 0)
  intro e he
  rw [ite_eq_right]
  rintro (h | h)
  · exact he (Or.inl (h.symm ▸ v.property))
  · exact he (Or.inr (h.symm ▸ v.property))

omit [Fintype V] [DecidableEq E] in
theorem onSide_degree_none (G : LooplessGraph V E) (S : Finset V) (x : E → ℝ) :
    (G.onSide S).degree (fun e => x e.val) none = G.cutMass x S := by
  simp only [degree, cutMass, cut, Finset.sum_filter]
  simp_rw [G.onSide_incident_none S]
  apply sum_subtype_supported (fun e => G.left e ∈ S ∨ G.right e ∈ S)
    (fun e => if G.Crosses S e then x e else 0)
  intro e he
  rw [ite_eq_right]
  rintro (h | h)
  · exact he (Or.inl h.1)
  · exact he (Or.inr h.2)

theorem odd_compl_of_even {W : Type uW} [Fintype W] [DecidableEq W]
    (hn : Even (Fintype.card W)) {T : Finset W} (hT : Odd T.card) : Odd Tᶜ.card := by
  rcases hn with ⟨k,hk⟩
  rcases hT with ⟨l,hl⟩
  have hle := Finset.card_le_univ T
  rw [Finset.card_compl]
  refine ⟨k-l-1, ?_⟩
  omega

omit [DecidableEq E] in

theorem restriction_mem_constraints (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) (S : Finset V) (hS : Odd S.card)
    (htight : G.cutMass x S = 1) :
    (fun e : {e // G.left e ∈ S ∨ G.right e ∈ S} => x e.val) ∈
      (G.onSide S).constraintPolytope := by
  refine ⟨fun e => hx.1 e.val, ?_, ?_⟩
  · intro v
    cases v with
    | none => exact (G.onSide_degree_none S x).trans htight
    | some v => exact (G.onSide_degree_some S x v).trans (hx.2.1 v.val)
  · intro T hT
    by_cases hn : none ∈ T
    · have hn' : none ∉ Tᶜ := by simpa using hn
      have hnEven : Even (Fintype.card (Option {v // v ∈ S})) := by
        simp only [Fintype.card_option, Fintype.card_coe]
        exact hS.add_odd odd_one
      have hTc := odd_compl_of_even hnEven hT
      have hh := hx.2.2 (liftVertices S Tᶜ) (by rwa [liftVertices_card S Tᶜ hn'])
      rw [← G.onSide_cutMass S x Tᶜ] at hh
      simpa only [cutMass, cut_compl] using hh
    · rw [G.onSide_cutMass S x T]
      exact hx.2.2 _ (by rwa [liftVertices_card S T hn])

end MatchingEntropyBounds.LooplessGraph

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds.LooplessGraph

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def supportSimple (G : LooplessGraph V E) (x : E → ℝ) : SimpleGraph V where
  Adj v w := ∃ e, 0 < x e ∧ ((G.left e=v ∧ G.right e=w) ∨ (G.left e=w ∧ G.right e=v))
  symm := ⟨by intro v w; rintro ⟨e,hx,h⟩; exact ⟨e,hx,h.symm⟩⟩
  loopless := ⟨by
    intro v
    rintro ⟨e,_,(⟨hl,hr⟩ | ⟨hl,hr⟩)⟩ <;> exact G.loopless e (hl.trans hr.symm)⟩

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
 theorem supportSimple_edge (G : LooplessGraph V E) {x : E → ℝ} {e : E} (he : 0 < x e) :
    (G.supportSimple x).Adj (G.left e) (G.right e) := ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩

theorem sum_pred_le_one {C : Type uC} [Fintype C] (P : C → Prop) [DecidablePred P]
    (huniq : ∀ a b, P a → P b → a=b) : (∑ c, if P c then (1 : ℝ) else 0) ≤ 1 := by
  by_cases h : ∃ a, P a
  · obtain ⟨a,ha⟩ := h
    rw [Finset.sum_eq_single a]
    · simp [ha]
    · intro b _ hb
      rw [ite_eq_right]
      intro hPb
      exact hb (huniq b a hPb ha)
    · simp
  · simp only [not_exists] at h
    simp [h]

omit [Fintype V] [DecidableEq E] in

theorem odd_family_bound (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {C : Type uC} [Fintype C] [DecidableEq C]
    (U : Finset V) (T : C → Finset V)
    (hodd : ∀ c, Odd (T c).card)
    (hdisj : ∀ c v, v ∈ T c → v ∉ U)
    (huniq : ∀ a b v, v ∈ T a → v ∈ T b → a=b)
    (hclosed : ∀ e, 0 < x e → G.left e ∉ U → G.right e ∉ U →
      ∀ c, G.left e ∈ T c ↔ G.right e ∈ T c) :
    Fintype.card C ≤ U.card := by
  have hcuts : (Fintype.card C : ℝ) ≤ ∑ c, G.cutMass x (T c) := by
    calc
      _ = ∑ c : C, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun c _ => hx.2.2 (T c) (hodd c)
  have hedges : ∀ e, (∑ c, if G.Crosses (T c) e then x e else 0) ≤
      (if G.left e ∈ U then x e else 0) + (if G.right e ∈ U then x e else 0) := by
    intro e
    by_cases hz : x e=0
    · simp [hz]
    have hp : 0 < x e := lt_of_le_of_ne (hx.1 e) (Ne.symm hz)
    by_cases hl : G.left e ∈ U <;> by_cases hr : G.right e ∈ U
    · have hzero : ∀ c, ¬G.Crosses (T c) e := by
        intro c hc
        rcases hc with h | h
        · exact hdisj c _ h.1 hl
        · exact hdisj c _ h.2 hr
      simp [hzero, hl, hr, hx.1 e]
    · have heq : ∀ c, G.Crosses (T c) e ↔ G.right e ∈ T c := by
        intro c
        have hn : G.left e ∉ T c := fun h => hdisj c _ h hl
        simp [Crosses, hn]
      simp_rw [heq]
      have hcount := sum_pred_le_one (fun c => G.right e ∈ T c)
        (fun a b => huniq a b (G.right e))
      have heq' : (∑ c, if G.right e ∈ T c then x e else 0) =
          (∑ c, if G.right e ∈ T c then (1 : ℝ) else 0) * x e := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        split <;> simp
      rw [heq']
      simpa [hl, hr] using mul_le_mul_of_nonneg_right hcount (hx.1 e)
    · have heq : ∀ c, G.Crosses (T c) e ↔ G.left e ∈ T c := by
        intro c
        have hn : G.right e ∉ T c := fun h => hdisj c _ h hr
        simp [Crosses, hn]
      simp_rw [heq]
      have hcount := sum_pred_le_one (fun c => G.left e ∈ T c)
        (fun a b => huniq a b (G.left e))
      have heq' : (∑ c, if G.left e ∈ T c then x e else 0) =
          (∑ c, if G.left e ∈ T c then (1 : ℝ) else 0) * x e := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        split <;> simp
      rw [heq']
      simpa [hl, hr] using mul_le_mul_of_nonneg_right hcount (hx.1 e)
    · have hzero : ∀ c, ¬G.Crosses (T c) e := by
        intro c hc
        have hiff := hclosed e hp hl hr c
        unfold Crosses at hc
        tauto
      simp [hzero, hl, hr]
  have hdegree : ∑ v ∈ U, G.degree x v = (U.card : ℝ) := by
    simp_rw [hx.2.1]
    simp
  have hsum : (∑ e : E, ((if G.left e ∈ U then x e else 0) +
      (if G.right e ∈ U then x e else 0))) = ∑ v ∈ U, G.degree x v := by
    simp only [degree]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    have hf : ∀ v, (if G.Incident v e then x e else 0) =
        (if G.left e = v then x e else 0) + (if G.right e = v then x e else 0) := by
      intro v
      by_cases hl : G.left e=v <;> by_cases hr : G.right e=v
      · exact (G.loopless e (hl.trans hr.symm)).elim
      all_goals simp [Incident, hl, hr]
    simp_rw [hf]
    rw [Finset.sum_add_distrib]
    simp
  have hbound := (Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hedges e))
  rw [hsum, hdegree] at hbound
  have hcutEq : (∑ c, G.cutMass x (T c)) = ∑ e, ∑ c, if G.Crosses (T c) e then x e else 0 := by
    simp only [cutMass, cut, Finset.sum_filter]
    exact Finset.sum_comm
  exact_mod_cast hcuts.trans (hcutEq ▸ hbound)

omit [DecidableEq E] in
theorem supportSimple_has_perfectMatching (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) :
    ∃ M : (G.supportSimple x).Subgraph, M.IsPerfectMatching := by
  classical
  apply SimpleGraph.tutte.mpr
  intro U
  let H := (⊤ : (G.supportSimple x).Subgraph).deleteVerts U
  let C := H.coe.oddComponents
  let : Fintype C := Fintype.ofFinite C
  let T : C → Finset V := fun c => (Subtype.val '' c.val.supp).toFinset
  have hnot : ∀ v : H.verts, v.val ∉ U := by
    intro v
    have hv := v.property
    simpa [H] using hv
  have hT : ∀ c : C, ∀ v : V, v ∈ T c ↔ ∃ w : H.verts, w ∈ c.val.supp ∧ w.val=v := by
    intro c v
    simp [T]
  have hodd : ∀ c : C, Odd (T c).card := by
    intro c
    have hc := c.property
    change Odd c.val.supp.ncard at hc
    change Odd ((Subtype.val '' c.val.supp).toFinset.card)
    rw [← Set.ncard_eq_toFinset_card', Set.ncard_image_of_injective _ Subtype.val_injective]
    exact hc
  have hdisj : ∀ c v, v ∈ T c → v ∉ U.toFinset := by
    intro c v hv
    obtain ⟨w,_,rfl⟩ := (hT c v).mp hv
    simpa using hnot w
  have huniq : ∀ a b v, v ∈ T a → v ∈ T b → a=b := by
    intro a b v ha hb
    obtain ⟨wa,hwa,rfl⟩ := (hT a v).mp ha
    obtain ⟨wb,hwb,he⟩ := (hT b wa.val).mp hb
    have hw : wb=wa := Subtype.ext he
    subst wb
    exact Subtype.ext (SimpleGraph.ConnectedComponent.eq_of_common_vertex hwa hwb)
  have hclosed : ∀ e, 0<x e → G.left e ∉ U.toFinset → G.right e ∉ U.toFinset →
      ∀ c, G.left e ∈ T c ↔ G.right e ∈ T c := by
    intro e he hl hr c
    have hl' : G.left e ∈ H.verts := by simpa [H] using hl
    have hr' : G.right e ∈ H.verts := by simpa [H] using hr
    have ha : H.Adj (G.left e) (G.right e) := by
      simpa [H, SimpleGraph.Subgraph.deleteVerts_adj] using
        And.intro hl (And.intro hr (G.supportSimple_edge he))
    change G.left e ∈ (Subtype.val '' c.val.supp).toFinset ↔
      G.right e ∈ (Subtype.val '' c.val.supp).toFinset
    simp only [Set.mem_toFinset]
    exact ⟨fun h => SimpleGraph.ConnectedComponent.mem_coe_supp_of_adj h hr' ha,
      fun h => SimpleGraph.ConnectedComponent.mem_coe_supp_of_adj h hl' ha.symm⟩
  have hb := G.odd_family_bound hx U.toFinset T hodd hdisj huniq hclosed
  change ¬ U.ncard < H.coe.oddComponents.ncard
  have hcard : Fintype.card C = H.coe.oddComponents.ncard := by
    simp [C, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rw [hcard] at hb
  exact not_lt_of_ge (by simpa only [← Set.ncard_eq_toFinset_card'] using hb)

theorem exists_supported_matching (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) :
    ∃ M : G.Matching, ∀ e ∈ M.val, 0 < x e := by
  classical
  obtain ⟨M,hM⟩ := G.supportSimple_has_perfectMatching hx
  have he : ∀ q ∈ M.edgeSet, ∃ e, 0<x e ∧ s(G.left e,G.right e)=q := by
    intro q
    induction q using Sym2.inductionOn with
    | hf v w =>
      intro hq
      obtain ⟨e,he,hor⟩ := (SimpleGraph.Subgraph.mem_edgeSet.mp hq).adj_sub
      refine ⟨e,he,Sym2.eq_iff.mpr hor⟩
  let f : M.edgeSet → E := fun q => (he q.val q.property).choose
  have hf : ∀ q, 0<x (f q) ∧ s(G.left (f q),G.right (f q))=q.val :=
    fun q => (he q.val q.property).choose_spec
  let F : Finset E := Finset.univ.image f
  have hF : G.IsPerfectMatching F := by
    intro v
    obtain ⟨w,hw,hu⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM v
    let q : M.edgeSet := ⟨s(v,w),SimpleGraph.Subgraph.mem_edgeSet.mpr hw⟩
    refine ⟨f q,⟨Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩,?_⟩,?_⟩
    · rcases Sym2.eq_iff.mp (hf q).2 with h | h
      · exact Or.inl h.1
      · exact Or.inr h.2
    · intro e he'
      obtain ⟨q',_,rfl⟩ := Finset.mem_image.mp he'.1
      have hq : q'=q := by
        apply Subtype.ext
        rcases he'.2 with hl | hr
        · have hval : q'.val=s(v,G.right (f q')) := by rw [← (hf q').2, hl]
          have hAdj : M.Adj v (G.right (f q')) :=
            SimpleGraph.Subgraph.mem_edgeSet.mp (hval ▸ q'.property)
          rw [hval, hu _ hAdj]
        · have hval : q'.val=s(v,G.left (f q')) := by
            rw [← (hf q').2, hr, Sym2.eq_swap]
          have hAdj : M.Adj v (G.left (f q')) :=
            SimpleGraph.Subgraph.mem_edgeSet.mp (hval ▸ q'.property)
          rw [hval, hu _ hAdj]
      exact congrArg f hq
  refine ⟨⟨F,hF⟩,?_⟩
  intro e he'
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp he'
  exact (hf q).1

omit [Fintype V] [Fintype E] [DecidableEq E] in
@[simp] theorem crosses_singleton (G : LooplessGraph V E) (v : V) (e : E) :
    G.Crosses {v} e ↔ G.Incident v e := by
  have hh := G.loopless e
  simp only [Crosses, Finset.mem_singleton, Incident]
  have hn : ¬ (G.left e=v ∧ G.right e=v) := fun h => hh (h.1.trans h.2.symm)
  tauto

omit [Fintype V] [DecidableEq E] in
@[simp] theorem cutMass_singleton (G : LooplessGraph V E) (x : E → ℝ) (v : V) :
    G.cutMass x {v} = G.degree x v := by
  simp [cutMass,cut,Finset.sum_filter,degree]

omit [DecidableEq E] in

theorem constraint_eventually_line (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) (u : E → ℝ)
    (hzero : ∀ e, x e=0 → u e=0) (hdeg : ∀ v, G.degree u v=0)
    (hcut : ∀ S, Odd S.card → G.cutMass x S=1 → G.cutMass u S=0) :
    ∀ᶠ t : ℝ in 𝓝 0, x+t • u ∈ G.constraintPolytope := by
  have hn : ∀ᶠ t : ℝ in 𝓝 0, ∀ e, 0≤(x+t • u) e := by
    apply Filter.eventually_all.mpr
    intro e
    by_cases he : x e=0
    · exact Filter.Eventually.of_forall (by intro t; simp [he,hzero e he])
    · have hp : 0<x e := lt_of_le_of_ne (hx.1 e) (Ne.symm he)
      have hc : Continuous (fun t : ℝ => (x+t • u) e) := by fun_prop
      have hh : ∀ᶠ t : ℝ in 𝓝 0, 0<(x+t • u) e := (isOpen_lt continuous_const hc).mem_nhds
        (by simpa using hp : 0<(x+(0:ℝ) • u) e)
      exact hh.mono fun t ht => ht.le
  have hodd : ∀ᶠ t : ℝ in 𝓝 0, ∀ S : Finset V, Odd S.card → 1≤G.cutMass (x+t • u) S := by
    apply Filter.eventually_all.mpr
    intro S
    by_cases hS : Odd S.card
    · by_cases ht : G.cutMass x S=1
      · exact Filter.Eventually.of_forall (by
          intro t _
          have he := G.cutMass_linear x u 1 t S
          simp only [one_smul, one_mul, hcut S hS ht, mul_zero, add_zero, ht] at he
          exact he.ge)
      · have hp : 1<G.cutMass x S := lt_of_le_of_ne (hx.2.2 S hS) (Ne.symm ht)
        have hc : Continuous (fun t : ℝ => G.cutMass (x+t • u) S) :=
          (G.continuous_cutMass S).comp (by fun_prop)
        have hh : ∀ᶠ t : ℝ in 𝓝 0, 1<G.cutMass (x+t • u) S := (isOpen_lt continuous_const hc).mem_nhds
          (by simpa using hp : 1<G.cutMass (x+(0:ℝ) • u) S)
        exact hh.mono fun t ht _ => ht.le
    · exact Filter.Eventually.of_forall fun _ h => (hS h).elim
  filter_upwards [hn,hodd] with t hn hodd
  refine ⟨hn,?_,hodd⟩
  intro v
  have he := G.degree_linear x u 1 t v
  simpa only [one_smul, one_mul, hdeg, mul_zero, add_zero, hx.2.1] using he

omit [Fintype V] [DecidableEq E] in
 theorem degree_sub (G : LooplessGraph V E) (x y : E → ℝ) (v : V) :
    G.degree (x-y) v = G.degree x v-G.degree y v := by
  have h := G.degree_linear x y 1 (-1) v
  simpa [sub_eq_add_neg] using h

omit [Fintype V] [DecidableEq E] in
 theorem cutMass_sub (G : LooplessGraph V E) (x y : E → ℝ) (S : Finset V) :
    G.cutMass (x-y) S = G.cutMass x S-G.cutMass y S := by
  have h := G.cutMass_linear x y 1 (-1) S
  simpa [sub_eq_add_neg] using h

omit [DecidableEq E] in

theorem trivial_tight_cut_preserved (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V))
    (hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1)
    (u : E → ℝ) (hdeg : ∀ v, G.degree u v=0) :
    ∀ S, Odd S.card → G.cutMass x S=1 → G.cutMass u S=0 := by
  intro S hS ht
  have hc := odd_compl_of_even heven hS
  have hsmall : S.card=1 ∨ Sᶜ.card=1 := by
    have hn : ¬ (3≤S.card ∧ 3≤Sᶜ.card) := fun h => hnt ⟨S,hS,h.1,h.2,ht⟩
    rcases hS with ⟨k,hk⟩
    rcases hc with ⟨l,hl⟩
    omega
  rcases hsmall with hs | hs
  · obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hs
    simpa using hdeg v
  · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hs
    have hh : G.cutMass u Sᶜ=0 := by rw [hv,cutMass_singleton,hdeg]
    simpa only [cutMass,cut_compl] using hh

 theorem extreme_no_tight_integral (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ Set.extremePoints ℝ G.constraintPolytope)
    (hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1) :
    ∃ M : G.Matching, G.indicator M=x := by
  have hxQ := (mem_extremePoints.mp hx).1
  obtain ⟨M,hM⟩ := G.exists_supported_matching hxQ
  have hd : ∀ v, G.degree (G.indicator M-x) v=0 := by
    intro v
    rw [degree_sub,degree_indicator,hxQ.2.1,sub_self]
  have hz : ∀ e, x e=0 → (G.indicator M-x) e=0 := by
    intro e he
    have hn : e ∉ M.val := fun h => (hM e h).ne' he
    simp [indicator,hn,he]
  have hu := G.constraint_eventually_line hxQ (G.indicator M-x) hz hd
    (G.trivial_tight_cut_preserved heven hnt _ hd)
  have he := extreme_point_direction_zero G.constraintPolytope hx _ hu
  exact ⟨M,sub_eq_zero.mp he⟩

theorem constraint_subset_polytope_aux (n : ℕ) :
    ∀ {W : Type uW} {F : Type uF} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
      (G : LooplessGraph W F), Fintype.card W=n → Even n →
      G.constraintPolytope ⊆ G.polytope := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W F _ _ _ _ G hcard heven
    have heven' : Even (Fintype.card W) := hcard ▸ heven
    have hex : Set.extremePoints ℝ G.constraintPolytope ⊆ G.polytope := by
      intro x hx
      have hxQ := (mem_extremePoints.mp hx).1
      by_cases hcut : ∃ S : Finset W, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1
      · obtain ⟨S,hS,hlo,hhi,ht⟩ := hcut
        have hc := odd_compl_of_even heven' hS
        have hlt1 : Fintype.card (Option {v // v ∈ S}) < n := by
          simp only [Fintype.card_option,Fintype.card_coe]
          have hco := Finset.card_compl S
          omega
        have hlt2 : Fintype.card (Option {v // v ∈ Sᶜ}) < n := by
          simp only [Fintype.card_option,Fintype.card_coe]
          have hco := Finset.card_compl S
          have hle := Finset.card_le_univ S
          omega
        have hv1 : Even (Fintype.card (Option {v // v ∈ S})) := by
          simpa only [Fintype.card_option,Fintype.card_coe] using hS.add_odd odd_one
        have hv2 : Even (Fintype.card (Option {v // v ∈ Sᶜ})) := by
          simpa only [Fintype.card_option,Fintype.card_coe] using hc.add_odd odd_one
        have hx1 := ih _ hlt1 (G.onSide S) rfl hv1 (G.restriction_mem_constraints hxQ S hS ht)
        have htc : G.cutMass x Sᶜ=1 := by simpa only [cutMass,cut_compl] using ht
        have hx2 := ih _ hlt2 (G.onSide Sᶜ) rfl hv2 (G.restriction_mem_constraints hxQ Sᶜ hc htc)
        obtain ⟨p,hp,hpx⟩ := ((G.onSide S).mem_polytope_iff _).mp hx1
        obtain ⟨q,hq,hqx⟩ := ((G.onSide Sᶜ).mem_polytope_iff _).mp hx2
        exact (G.mem_polytope_iff x).mpr (G.couple_laws S x hp hq (congrFun hpx) (congrFun hqx))
      · obtain ⟨M,rfl⟩ := G.extreme_no_tight_integral heven' hx hcut
        exact subset_convexHull ℝ _ (Set.mem_range_self M)
    rw [← closure_convexHull_extremePoints G.isCompact_constraintPolytope G.convex_constraintPolytope]
    exact closure_minimal (convexHull_min hex (convex_convexHull ℝ _)) G.compact_polytope.isClosed

theorem polytope_eq_constraints (G : LooplessGraph V E) (heven : Even (Fintype.card V)) :
    G.polytope = G.constraintPolytope := by
  exact Set.Subset.antisymm G.polytope_subset_constraintPolytope
    (constraint_subset_polytope_aux (Fintype.card V) G rfl heven)

end MatchingEntropyBounds.LooplessGraph

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds.LooplessGraph

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def positiveExtension (x : E → ℝ) : ({e // 0<x e} → ℝ) →ₗ[ℝ] (E → ℝ) := by
  classical
  exact {
    toFun := fun u e => if h : 0<x e then u ⟨e,h⟩ else 0
    map_add' := by intro u v; ext e; by_cases h : 0<x e <;> simp [h]
    map_smul' := by intro a u; ext e; by_cases h : 0<x e <;> simp [h] }

omit [Fintype E] [DecidableEq E] in
@[simp] theorem positiveExtension_pos (x : E → ℝ) (u : {e // 0<x e} → ℝ)
    (e : {e // 0<x e}) : positiveExtension x u e.val=u e := by
  simp [positiveExtension,e.property]

omit [Fintype E] [DecidableEq E] in
@[simp] theorem positiveExtension_zero (x : E → ℝ) (u : {e // 0<x e} → ℝ)
    {e : E} (he : x e=0) : positiveExtension x u e=0 := by
  simp [positiveExtension,he]

def degreeLinear (G : LooplessGraph V E) : (E → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun := G.degree
  map_add' := by
    intro u v
    ext w
    simpa using G.degree_linear u v 1 1 w
  map_smul' := by
    intro a u
    ext w
    simp only [degree,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    split <;> simp

def cutLinear (G : LooplessGraph V E) (S : Finset V) : (E → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun u => G.cutMass u S
  map_add' := by intro u v; simpa using G.cutMass_linear u v 1 1 S
  map_smul' := by intro a u; simp [cutMass,Finset.mul_sum]

def faceSpace (G : LooplessGraph V E) (x : E → ℝ) : Submodule ℝ ({e // 0<x e} → ℝ) where
  carrier := {u | G.degreeLinear (positiveExtension x u)=0 ∧
    ∀ S : Finset V, Odd S.card → G.cutMass x S=1 → G.cutLinear S (positiveExtension x u)=0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    refine ⟨by simp only [map_add,hu.1,hv.1,add_zero],?_⟩
    intro S hS ht
    simp only [map_add,hu.2 S hS ht,hv.2 S hS ht,add_zero]
  smul_mem' := by
    intro a u hu
    refine ⟨by simp only [map_smul,hu.1,smul_zero],?_⟩
    intro S hS ht
    simp only [map_smul,hu.2 S hS ht,smul_zero]

def faceCodimension (G : LooplessGraph V E) (x : E → ℝ) : ℕ :=
  Module.finrank ℝ (({e // 0<x e} → ℝ) ⧸ G.faceSpace x)

omit [DecidableEq E] in
 theorem faceCodimension_no_tight (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V))
    (hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1) :
    G.faceCodimension x ≤ Fintype.card V := by
  classical
  let F := G.degreeLinear.comp (positiveExtension x)
  have hk : F.ker ≤ G.faceSpace x := by
    intro u hu
    have hd : G.degreeLinear (positiveExtension x u)=0 := hu
    refine ⟨hd,?_⟩
    exact G.trivial_tight_cut_preserved heven hnt _ (congrFun hd)
  simpa [faceCodimension] using quotient_finrank_le_of_ker_le (G.faceSpace x) F hk

omit [DecidableEq E] in
 theorem faceSpace_eventually_line (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {u : {e // 0<x e} → ℝ} (hu : u ∈ G.faceSpace x) :
    ∀ᶠ t : ℝ in 𝓝 0, x+t • positiveExtension x u ∈ G.constraintPolytope := by
  exact G.constraint_eventually_line hx _ (fun e he => positiveExtension_zero x u he)
    (congrFun hu.1) hu.2

omit [Fintype V] [DecidableEq E] in
 theorem faceSpace_of_eventually_line (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {u : {e // 0<x e} → ℝ}
    (hu : ∀ᶠ t : ℝ in 𝓝 0, x+t • positiveExtension x u ∈ G.constraintPolytope) :
    u ∈ G.faceSpace x := by
  have hu' : ∀ᶠ t : ℝ in 𝓝 0, x+(-t) • positiveExtension x u ∈ G.constraintPolytope := by
    have hc : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by simpa using continuous_neg.tendsto (0:ℝ)
    exact hc.eventually hu
  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (x+t • positiveExtension x u ∈ G.constraintPolytope ∧
        x+(-t) • positiveExtension x u ∈ G.constraintPolytope) ∧ 0<t :=
    ((hu.and hu').filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  obtain ⟨a,⟨ha,hna⟩,ha0⟩ := hh.exists
  refine ⟨?_,?_⟩
  · ext v
    have he := G.degree_linear x (positiveExtension x u) 1 a v
    simp only [one_smul,one_mul,hx.2.1,ha.2.1] at he
    change G.degree (positiveExtension x u) v=0
    nlinarith
  · intro S hS ht
    have he := G.cutMass_linear x (positiveExtension x u) 1 a S
    have he' := G.cutMass_linear x (positiveExtension x u) 1 (-a) S
    simp only [one_smul,one_mul,ht] at he he'
    have hp := ha.2.2 S hS
    have hn := hna.2.2 S hS
    change G.cutMass (positiveExtension x u) S=0
    nlinarith

abbrev sideMarginal (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) :
    {e // G.left e ∈ S ∨ G.right e ∈ S} → ℝ := fun e => x e.val

def sideRestriction (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) :
    ({e // 0<x e} → ℝ) →ₗ[ℝ] ({e // 0<G.sideMarginal x S e} → ℝ) where
  toFun := fun u e => u ⟨e.val.val,e.property⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
 theorem positiveExtension_side (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V)
    (u : {e // 0<x e} → ℝ) (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    positiveExtension (G.sideMarginal x S) (G.sideRestriction x S u) e =
      positiveExtension x u e.val := by
  rfl

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
 theorem sideMarginal_line (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V)
    (u : {e // 0<x e} → ℝ) (t : ℝ) :
    G.sideMarginal (x+t • positiveExtension x u) S = G.sideMarginal x S +
      t • positiveExtension (G.sideMarginal x S) (G.sideRestriction x S u) := by
  rfl

theorem faceSpace_of_side_spaces (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.constraintPolytope)
    (S : Finset V) (hS : Odd S.card) (ht : G.cutMass x S=1)
    {u : {e // 0<x e} → ℝ}
    (h1 : G.sideRestriction x S u ∈ (G.onSide S).faceSpace (G.sideMarginal x S))
    (h2 : G.sideRestriction x Sᶜ u ∈ (G.onSide Sᶜ).faceSpace (G.sideMarginal x Sᶜ)) :
    u ∈ G.faceSpace x := by
  have hc := odd_compl_of_even heven hS
  have htc : G.cutMass x Sᶜ=1 := by simpa only [cutMass,cut_compl] using ht
  have hx1 := G.restriction_mem_constraints hx S hS ht
  have hx2 := G.restriction_mem_constraints hx Sᶜ hc htc
  have hv1 : Even (Fintype.card (Option {v // v ∈ S})) := by
    simpa only [Fintype.card_option,Fintype.card_coe] using hS.add_odd odd_one
  have hv2 : Even (Fintype.card (Option {v // v ∈ Sᶜ})) := by
    simpa only [Fintype.card_option,Fintype.card_coe] using hc.add_odd odd_one
  apply G.faceSpace_of_eventually_line hx
  filter_upwards [(G.onSide S).faceSpace_eventually_line hx1 h1,
    (G.onSide Sᶜ).faceSpace_eventually_line hx2 h2] with t ht1 ht2
  rw [← G.sideMarginal_line x S u t] at ht1
  rw [← G.sideMarginal_line x Sᶜ u t] at ht2
  have hp1 : G.sideMarginal (x+t • positiveExtension x u) S ∈ (G.onSide S).polytope := by
    rwa [(G.onSide S).polytope_eq_constraints hv1]
  have hp2 : G.sideMarginal (x+t • positiveExtension x u) Sᶜ ∈ (G.onSide Sᶜ).polytope := by
    rwa [(G.onSide Sᶜ).polytope_eq_constraints hv2]
  obtain ⟨p,hp,hpx⟩ := ((G.onSide S).mem_polytope_iff _).mp hp1
  obtain ⟨q,hq,hqx⟩ := ((G.onSide Sᶜ).mem_polytope_iff _).mp hp2
  have hp := (G.mem_polytope_iff _).mpr (G.couple_laws S _ hp hq (congrFun hpx) (congrFun hqx))
  exact G.polytope_subset_constraintPolytope hp

 theorem faceCodimension_le_sides (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.constraintPolytope)
    (S : Finset V) (hS : Odd S.card) (ht : G.cutMass x S=1) :
    G.faceCodimension x ≤ (G.onSide S).faceCodimension (G.sideMarginal x S) +
      (G.onSide Sᶜ).faceCodimension (G.sideMarginal x Sᶜ) := by
  classical
  exact quotient_finrank_le_pair (G.faceSpace x) ((G.onSide S).faceSpace (G.sideMarginal x S))
    ((G.onSide Sᶜ).faceSpace (G.sideMarginal x Sᶜ))
    (G.sideRestriction x S) (G.sideRestriction x Sᶜ)
    (fun _ => G.faceSpace_of_side_spaces heven hx S hS ht)

theorem faceCodimension_strong_aux (n : ℕ) :
    ∀ {W : Type uW} {F : Type uF} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
      (G : LooplessGraph W F), Fintype.card W=n → Even n → 4≤n →
      ∀ x ∈ G.constraintPolytope, G.faceCodimension x ≤ 2*(n-2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W F _ _ _ _ G hcard heven hfour x hx
    have heven' : Even (Fintype.card W) := hcard ▸ heven
    by_cases hcut : ∃ S : Finset W, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1
    · obtain ⟨S,hS,hlo,hhi,ht⟩ := hcut
      have hc := odd_compl_of_even heven' hS
      have hlt1 : Fintype.card (Option {v // v ∈ S}) < n := by
        simp only [Fintype.card_option,Fintype.card_coe]
        have hco := Finset.card_compl S
        omega
      have hlt2 : Fintype.card (Option {v // v ∈ Sᶜ}) < n := by
        simp only [Fintype.card_option,Fintype.card_coe]
        have hco := Finset.card_compl S
        have hle := Finset.card_le_univ S
        omega
      have hv1 : Even (Fintype.card (Option {v // v ∈ S})) := by
        simpa only [Fintype.card_option,Fintype.card_coe] using hS.add_odd odd_one
      have hv2 : Even (Fintype.card (Option {v // v ∈ Sᶜ})) := by
        simpa only [Fintype.card_option,Fintype.card_coe] using hc.add_odd odd_one
      have hn1 : 4≤Fintype.card (Option {v // v ∈ S}) := by
        simp only [Fintype.card_option,Fintype.card_coe]; omega
      have hn2 : 4≤Fintype.card (Option {v // v ∈ Sᶜ}) := by
        simp only [Fintype.card_option,Fintype.card_coe]; omega
      have hx1 := G.restriction_mem_constraints hx S hS ht
      have htc : G.cutMass x Sᶜ=1 := by simpa only [cutMass,cut_compl] using ht
      have hx2 := G.restriction_mem_constraints hx Sᶜ hc htc
      have hb1 := ih _ hlt1 (G.onSide S) rfl hv1 hn1 _ hx1
      have hb2 := ih _ hlt2 (G.onSide Sᶜ) rfl hv2 hn2 _ hx2
      have hb := G.faceCodimension_le_sides heven' hx S hS ht
      have hsum : Fintype.card (Option {v // v ∈ S}) + Fintype.card (Option {v // v ∈ Sᶜ})=n+2 := by
        simp only [Fintype.card_option,Fintype.card_coe]
        have hh := Finset.card_compl_add_card S
        omega
      change (G.onSide S).faceCodimension (G.sideMarginal x S) ≤ _ at hb1
      change (G.onSide Sᶜ).faceCodimension (G.sideMarginal x Sᶜ) ≤ _ at hb2
      omega
    · have hb := G.faceCodimension_no_tight heven' hcut
      omega

theorem faceCodimension_bound (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.polytope) :
    G.faceCodimension x ≤ 2*Fintype.card V := by
  by_cases hn : 4≤Fintype.card V
  · have hb := faceCodimension_strong_aux (Fintype.card V) G rfl heven hn x
      (G.polytope_subset_constraintPolytope hx)
    omega
  · have hnt : ¬ ∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1 := by
      rintro ⟨S,_,hlo,hhi,_⟩
      have hh := Finset.card_compl_add_card S
      omega
    have hb := G.faceCodimension_no_tight heven hnt
    omega

omit [Fintype V] [DecidableEq E] in
 theorem degree_add_smul (G : LooplessGraph V E) (x u : E → ℝ) (t : ℝ) (v : V) :
    G.degree (x+t • u) v=G.degree x v+t*G.degree u v := by
  simpa using G.degree_linear x u 1 t v

omit [Fintype V] [DecidableEq E] in
 theorem cutMass_add_smul (G : LooplessGraph V E) (x u : E → ℝ) (t : ℝ) (S : Finset V) :
    G.cutMass (x+t • u) S=G.cutMass x S+t*G.cutMass u S := by
  simpa using G.cutMass_linear x u 1 t S

omit [DecidableEq E] in

theorem constraint_eventually_expand (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {t : ℝ} (ht : 0<t) :
    ∀ᶠ y in 𝓝[G.constraintPolytope] x, x+t⁻¹ • (y-x) ∈ G.constraintPolytope := by
  have hn : ∀ᶠ y in 𝓝[G.constraintPolytope] x, ∀ e, 0≤(x+t⁻¹ • (y-x)) e := by
    apply Filter.eventually_all.mpr
    intro e
    by_cases he : x e=0
    · filter_upwards [eventually_mem_nhdsWithin] with y hy
      simpa [he] using mul_nonneg (inv_nonneg.mpr ht.le) (hy.1 e)
    · have hp : 0<x e := lt_of_le_of_ne (hx.1 e) (Ne.symm he)
      have hc : Continuous (fun y : E → ℝ => (x+t⁻¹ • (y-x)) e) := by fun_prop
      have hh : ∀ᶠ y : E → ℝ in 𝓝 x, 0<(x+t⁻¹ • (y-x)) e :=
        (isOpen_lt continuous_const hc).mem_nhds (by simpa using hp)
      exact (hh.filter_mono nhdsWithin_le_nhds).mono fun y hy => hy.le
  have hodd : ∀ᶠ y in 𝓝[G.constraintPolytope] x,
      ∀ S : Finset V, Odd S.card → 1≤G.cutMass (x+t⁻¹ • (y-x)) S := by
    apply Filter.eventually_all.mpr
    intro S
    by_cases hS : Odd S.card
    · by_cases hs : G.cutMass x S=1
      · filter_upwards [eventually_mem_nhdsWithin] with y hy _
        rw [cutMass_add_smul,cutMass_sub,hs]
        have hh := mul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr (hy.2.2 S hS))
        linarith
      · have hp : 1<G.cutMass x S := lt_of_le_of_ne (hx.2.2 S hS) (Ne.symm hs)
        have hc : Continuous (fun y : E → ℝ => G.cutMass (x+t⁻¹ • (y-x)) S) :=
          (G.continuous_cutMass S).comp (by fun_prop)
        have hh : ∀ᶠ y : E → ℝ in 𝓝 x, 1<G.cutMass (x+t⁻¹ • (y-x)) S :=
          (isOpen_lt continuous_const hc).mem_nhds (by simpa using hp)
        exact (hh.filter_mono nhdsWithin_le_nhds).mono fun y hy _ => hy.le
    · exact Filter.Eventually.of_forall fun _ h => (hS h).elim
  filter_upwards [hn,hodd,eventually_mem_nhdsWithin] with y hn hodd hy
  refine ⟨hn,?_,hodd⟩
  intro v
  rw [degree_add_smul,degree_sub,hx.2.1,hy.2.1]
  ring

 theorem polytope_eventually_expand (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.polytope) {t : ℝ} (ht : 0<t) :
    ∀ᶠ y in 𝓝[G.polytope] x, x+t⁻¹ • (y-x) ∈ G.polytope := by
  rw [G.polytope_eq_constraints heven] at hx ⊢
  exact G.constraint_eventually_expand hx ht

end MatchingEntropyBounds.LooplessGraph

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def marginalEntropy (y : E → ℝ) : ℝ := entropy y

theorem entropy_eq {ι : Type uι} [Fintype ι] (p : ι → ℝ) :
    entropy p = -(∑ i, p i * Real.log (p i)) := by
  simp [entropy, Real.negMulLog, Finset.sum_neg_distrib, neg_mul]

theorem continuous_entropy {ι : Type uι} [Fintype ι] :
    Continuous (entropy : (ι → ℝ) → ℝ) := by
  unfold entropy
  fun_prop

theorem entropy_nonneg {ι : Type uι} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) : 0 ≤ entropy p := by
  apply Finset.sum_nonneg
  intro i _
  exact Real.negMulLog_nonneg (mem_Icc_of_mem_probabilitySimplex hp i).1
    (mem_Icc_of_mem_probabilitySimplex hp i).2

theorem entropy_le_log_card {ι : Type uι} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) : entropy p ≤ Real.log (Fintype.card ι) := by
  have hn : 0 < Fintype.card ι := by
    by_contra h
    have hz : Fintype.card ι = 0 := Nat.eq_zero_of_not_pos h
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hz
    simpa using hp.2
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    Real.negMulLog_le_one_sub_self (mul_nonneg hnR.le (hp.1 i)))
  simp_rw [Real.negMulLog_mul] at h
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    hp.2, one_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hp.2] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, sub_self] at h
  change Real.negMulLog (Fintype.card ι) + (Fintype.card ι : ℝ) * entropy p ≤ 0 at h
  rw [Real.negMulLog] at h
  nlinarith

namespace LooplessGraph

omit [Fintype V] [DecidableEq V] in
theorem coordinate_mem_Icc (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) (e : E) : y e ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨p, hp, rfl⟩ := (G.mem_polytope_iff y).mp hy
  constructor
  · exact Finset.sum_nonneg (fun M _ ↦ mul_nonneg (hp.1 M) (G.indicator_nonneg M e))
  · calc
      ∑ M, p M * G.indicator M e ≤ ∑ M, p M * 1 :=
        Finset.sum_le_sum (fun M _ ↦ mul_le_mul_of_nonneg_left (G.indicator_le_one M e) (hp.1 M))
      _ = 1 := by simpa using hp.2

omit [Fintype E] [DecidableEq E] in

theorem incident_vertex_sum (G : LooplessGraph V E) (e : E) :
    (∑ v, if G.Incident v e then (1 : ℕ) else 0) = 2 := by
  classical
  have he (v : V) : (if G.Incident v e then (1 : ℕ) else 0) =
      (if G.left e = v then 1 else 0) + (if G.right e = v then 1 else 0) := by
    by_cases hl : G.left e = v <;> by_cases hr : G.right e = v
    · exact False.elim (G.loopless e (hl.trans hr.symm))
    · simp [Incident, hl, hr]
    · simp [Incident, hl, hr]
    · simp [Incident, hl, hr]
  simp_rw [he, Finset.sum_add_distrib]
  simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem matching_incident_sum (G : LooplessGraph V E) (M : G.Matching) (v : V) :
    (∑ e ∈ M.val, if G.Incident v e then (1 : ℕ) else 0) = 1 := by
  classical
  obtain ⟨e, ⟨he, hv⟩, hu⟩ := M.property v
  rw [Finset.sum_eq_single e]
  · simp [hv]
  · intro e' he' hne
    have hn : ¬ G.Incident v e' := fun hv' ↦ hne (hu e' ⟨he', hv'⟩)
    simp [hn]
  · simp [he]

omit [Fintype E] [DecidableEq E] in
theorem matching_card_twice (G : LooplessGraph V E) (M : G.Matching) :
    2 * M.val.card = Fintype.card V := by
  classical
  calc
    2 * M.val.card = ∑ e ∈ M.val, ∑ v, if G.Incident v e then (1 : ℕ) else 0 := by
      simp_rw [G.incident_vertex_sum]
      simp [Nat.mul_comm]
    _ = ∑ v, ∑ e ∈ M.val, if G.Incident v e then (1 : ℕ) else 0 := Finset.sum_comm
    _ = Fintype.card V := by
      simp_rw [G.matching_incident_sum]
      simp

omit [Fintype E] [DecidableEq E] in
theorem matching_card (G : LooplessGraph V E) {m : ℕ}
    (hV : Fintype.card V = 2 * m) (M : G.Matching) : M.val.card = m := by
  have h := G.matching_card_twice M
  omega

theorem indicator_sum (G : LooplessGraph V E) {m : ℕ}
    (hV : Fintype.card V = 2 * m) (M : G.Matching) :
    ∑ e, G.indicator M e = (m : ℝ) := by
  simp [indicator, G.matching_card hV M]

theorem marginal_sum (G : LooplessGraph V E) {m : ℕ}
    (hV : Fintype.card V = 2 * m) {y : E → ℝ} (hy : y ∈ G.polytope) :
    ∑ e, y e = (m : ℝ) := by
  obtain ⟨p, hp, rfl⟩ := (G.mem_polytope_iff y).mp hy
  simp_rw [mean]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, G.indicator_sum hV]
  rw [← Finset.sum_mul, hp.2, one_mul]

end LooplessGraph

omit [Fintype V] [DecidableEq V] in

theorem maxMatchingEntropy_attained (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) :
    ∃ p ∈ G.feasibleLaws y, entropy p = maxMatchingEntropy G y := by
  have hc := (G.compact_feasibleLaws y).image continuous_entropy
  have hn := ((G.mem_polytope_iff y).mp hy).image entropy
  obtain ⟨p, hp, hpe⟩ := hc.sSup_mem hn
  exact ⟨p, hp, hpe⟩

omit [Fintype V] [DecidableEq V] in
theorem maxMatchingEntropy_nonneg (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) : 0 ≤ maxMatchingEntropy G y := by
  obtain ⟨p, hp, he⟩ := maxMatchingEntropy_attained G hy
  rw [← he]
  exact entropy_nonneg hp.1

omit [Fintype V] [DecidableEq V] in
theorem maxMatchingEntropy_le_log_card (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) :
    maxMatchingEntropy G y ≤ Real.log (Fintype.card G.Matching) := by
  obtain ⟨p, hp, he⟩ := maxMatchingEntropy_attained G hy
  rw [← he]
  exact entropy_le_log_card hp.1

omit [Fintype V] [DecidableEq V] in
theorem entropy_le_maxMatchingEntropy (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y) :
    entropy p ≤ maxMatchingEntropy G y := by
  apply le_csSup
  · exact ((G.compact_feasibleLaws y).image continuous_entropy).bddAbove
  · exact ⟨p, hp, rfl⟩

end MatchingEntropyBounds

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem entropy_mix_ge {ι : Type uι} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1-t) * entropy p + t * entropy q ≤
      entropy (fun i => (1-t)*p i + t*q i) := by
  unfold entropy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.2
    (hp i) (hq i) (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)

theorem entropy_mix_zero_bonus {ι : Type uι} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) {j : ι} (hj : p j = 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1-t) * entropy p + t * entropy q + q j * Real.negMulLog t ≤
      entropy (fun i => (1-t)*p i + t*q i) := by
  classical
  have hterm : ∀ i, (1-t) * Real.negMulLog (p i) + t * Real.negMulLog (q i) +
      (if i=j then q j * Real.negMulLog t else 0) ≤
        Real.negMulLog ((1-t)*p i+t*q i) := by
    intro i
    by_cases hi : i=j
    · subst i
      simp only [hj, Real.negMulLog_zero, mul_zero, zero_add, ite_true,
        Real.negMulLog_mul]
      linarith
    · simp only [hi, ↓reduceIte, add_zero]
      simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.2
        (hp i) (hq i) (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, entropy] using hh

theorem entropy_maximizer_support {ι : Type uι} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hmax : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      entropy (fun i => (1-t)*p i+t*q i) ≤ entropy p) {j : ι} (hjq : 0 < q j) :
    0 < p j := by
  by_contra hj
  have hj0 : p j = 0 := le_antisymm (le_of_not_gt hj) (hp j)
  have hqp : entropy q ≤ entropy p := by simpa using hmax 1 (by constructor <;> norm_num)
  let c := (entropy p-entropy q)/(q j)+1
  have hc : 0 < c := by dsimp [c]; positivity
  let t := Real.exp (-c)
  have htp : 0 < t := Real.exp_pos _
  have ht : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨htp.le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hc.le)⟩
  have hbonus := (entropy_mix_zero_bonus hp hq hj0 ht).trans (hmax t ht)
  have hlog : Real.log t = -c := Real.log_exp _
  rw [Real.negMulLog, hlog] at hbonus
  have he : q j * c = entropy p-entropy q+q j := by
    dsimp [c]
    field_simp
  nlinarith

omit [Fintype V] [DecidableEq V] in

theorem matching_optimizer_support (G : LooplessGraph V E) {y : E → ℝ}
    {p q : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hq : q ∈ G.feasibleLaws y) (hopt : entropy p = maxMatchingEntropy G y)
    {M : G.Matching} (hM : 0 < q M) : 0 < p M := by
  apply entropy_maximizer_support hp.1.1 hq.1.1 _ hM
  intro t ht
  apply le_trans (entropy_le_maxMatchingEntropy (G := G) (y := y) ?_) (le_of_eq hopt.symm)
  constructor
  · exact convex_probabilitySimplex _ hp.1 hq.1
      (sub_nonneg.mpr ht.2) ht.1 (by ring)
  · calc
      G.mean (fun i => (1-t)*p i+t*q i) =
          (1-t) • G.mean p + t • G.mean q := by
        exact (G.meanLinear).map_add ((1-t) • p) (t • q) |>.trans (by
          rw [LinearMap.map_smul, LinearMap.map_smul]; rfl)
      _ = y := by rw [hp.2, hq.2]; ext e; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem negMulLog_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    Real.negMulLog x ≤ -x * Real.log y + y-x := by
  have h := mul_le_mul_of_nonneg_left
    (Real.negMulLog_le_one_sub_self (div_nonneg hx hy.le)) hy.le
  have he : Real.negMulLog x = -x * Real.log y + y * Real.negMulLog (x/y) := by
    calc
      Real.negMulLog x = Real.negMulLog (y * (x/y)) := by congr 1; field_simp
      _ = (x/y) * Real.negMulLog y + y * Real.negMulLog (x/y) := Real.negMulLog_mul _ _
      _ = _ := by unfold Real.negMulLog; field_simp
  rw [he]
  have hdiv : y * (x/y) = x := by field_simp
  nlinarith

theorem entropy_le_crossEntropy {ι : Type uι} [Fintype ι] {p q : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (hq : q ∈ probabilitySimplex ι)
    (hsupp : ∀ i, p i = 0 → q i = 0) :
    entropy q ≤ -∑ i, q i * Real.log (p i) := by
  have hterm : ∀ i, Real.negMulLog (q i) ≤
      -(q i * Real.log (p i)) + p i-q i := by
    intro i
    by_cases hi : p i = 0
    · simp [hi, hsupp i hi]
    · simpa only [neg_mul] using negMulLog_tangent (hq.1 i)
        (lt_of_le_of_ne (hp.1 i) (Ne.symm hi))
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ => hterm i
  simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, hp.2, hq.2, add_sub_cancel_right, entropy] using hh

theorem entropy_line_hasDerivAt {ι : Type uι} [Fintype ι] (p v : ι → ℝ)
    (hsupp : ∀ i, p i = 0 → v i = 0) :
    HasDerivAt (fun t : ℝ => entropy (fun i => p i+t*v i))
      (-∑ i, v i * Real.log (p i) - ∑ i, v i) 0 := by
  have hd : ∀ i, HasDerivAt (fun t : ℝ => Real.negMulLog (p i+t*v i))
      ((-Real.log (p i)-1)*v i) 0 := by
    intro i
    by_cases hi : p i = 0
    · simpa only [hi, hsupp i hi, mul_zero, add_zero, Real.negMulLog_zero] using
        (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    · have hp : p i+(0 : ℝ)*v i ≠ 0 := by simpa using hi
      simpa only [zero_mul, add_zero, one_mul, Function.comp_def, id_eq] using
        (Real.hasDerivAt_negMulLog hp).comp 0
          (((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (p i))
  have he : (∑ i, (-Real.log (p i)-1)*v i) =
      -∑ i, v i*Real.log (p i) - ∑ i, v i := by
    simp_rw [sub_mul, one_mul, neg_mul, mul_comm (Real.log (p _))]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [← he]
  simpa only [entropy, Finset.sum_apply] using (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i))

omit [Fintype V] [DecidableEq V] in

theorem matching_optimizer_log_annihilates (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y) (v : G.Matching → ℝ)
    (hvsum : ∑ M, v M = 0) (hvmean : G.mean v = 0)
    (hsupp : ∀ M, p M = 0 → v M = 0) :
    ∑ M, v M * Real.log (p M) = 0 := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ M, 0 ≤ p M+t*v M := by
    apply Filter.eventually_all.mpr
    intro M
    by_cases hM : p M = 0
    · exact Filter.Eventually.of_forall (fun t => by simp [hM, hsupp M hM])
    · have hpos : 0 < p M := lt_of_le_of_ne (hp.1.1 M) (Ne.symm hM)
      have hc : Continuous (fun t : ℝ => p M+t*v M) := by fun_prop
      have hh : {t : ℝ | 0 < p M+t*v M} ∈ 𝓝 0 :=
        (isOpen_lt continuous_const hc).mem_nhds (by simpa using hpos)
      exact Filter.Eventually.mono hh (fun t ht => ht.le)
  have hlocal : IsLocalMax (fun t : ℝ => entropy (fun M => p M+t*v M)) 0 := by
    filter_upwards [hev] with t ht
    have hmean : G.mean (fun M => p M+t*v M) = y := by
      change G.meanLinear (p+t • v) = y
      rw [map_add, map_smul]
      change G.mean p + t • G.mean v = y
      rw [hp.2, hvmean, smul_zero, add_zero]
    have hsum : ∑ M, (p M+t*v M) = 1 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp.1.2, hvsum, mul_zero, add_zero]
    have hle := entropy_le_maxMatchingEntropy (G := G) ⟨⟨ht, hsum⟩, hmean⟩
    simpa only [zero_mul, add_zero, ← hopt] using hle
  have hh := hlocal.deriv_eq_zero
  rw [(entropy_line_hasDerivAt p v hsupp).deriv, hvsum] at hh
  linarith

theorem exists_pos_nonneg_perturb {ι : Type uι} [Fintype ι] (p v : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hz : ∀ i, p i = 0 → 0 ≤ v i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, 0 ≤ p i+t*v i := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, p i ≠ 0 → 0 ≤ p i+t*v i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : p i = 0
    · exact Filter.Eventually.of_forall (fun _ h => (h hi).elim)
    · have hc : Continuous (fun t : ℝ => p i+t*v i) := by fun_prop
      have hh : {t : ℝ | 0 < p i+t*v i} ∈ 𝓝 0 :=
        (isOpen_lt continuous_const hc).mem_nhds
          (by simpa using lt_of_le_of_ne (hp i) (Ne.symm hi))
      exact Filter.Eventually.mono hh (fun t ht _ => ht.le)
  have he' := (hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Set.Ioi 0)
  obtain ⟨t, ht, htp⟩ := he'.exists
  refine ⟨t, htp, fun i => ?_⟩
  by_cases hi : p i = 0
  · rw [hi, zero_add]
    exact mul_nonneg htp.le (hz i hi)
  · exact ht i hi

omit [Fintype V] [DecidableEq V] in

theorem matching_optimizer_face_support (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y)
    {q r : G.Matching → ℝ} (hq : q ∈ probabilitySimplex G.Matching)
    (hr : r ∈ probabilitySimplex G.Matching) (hmean : G.mean q = G.mean r)
    (hrsupport : ∀ M, p M = 0 → r M = 0) :
    ∀ M, p M = 0 → q M = 0 := by
  obtain ⟨t, htp, ht⟩ := exists_pos_nonneg_perturb p (q-r) hp.1.1
    (fun M hM => by simpa [hrsupport M hM] using hq.1 M)
  have hsum : ∑ M, (p M+t*(q-r) M) = 1 := by
    simp only [Pi.sub_apply, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, hp.1.2, hq.2, hr.2]
    ring
  have hmean' : G.mean (fun M => p M+t*(q-r) M) = y := by
    change G.meanLinear (p+t • (q-r)) = y
    rw [map_add, map_smul, map_sub]
    change G.mean p + t • (G.mean q-G.mean r) = y
    rw [hp.2, hmean, sub_self, smul_zero, add_zero]
  intro M hM
  by_contra hqM
  have hqMp : 0 < q M := lt_of_le_of_ne (hq.1 M) (Ne.symm hqM)
  have hpM := matching_optimizer_support G hp ⟨⟨ht, hsum⟩, hmean'⟩ hopt
    (M := M) (by simpa [hM, hrsupport M hM] using mul_pos htp hqMp)
  simp [hM] at hpM

end MatchingEntropyBounds

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def partition {ι : Type uι} [Fintype ι] (p a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, p i * Real.exp (t*a i)

def tiltedLaw {ι : Type uι} [Fintype ι] (p a : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  p i * Real.exp (t*a i) / partition p a t

theorem partition_pos {ι : Type uι} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (t : ℝ) : 0 < partition p a t := by
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hp.1 i)).mp
    (show 0 < ∑ i, p i by rw [hp.2]; norm_num)
  exact (Finset.sum_pos_iff_of_nonneg (fun i _ => mul_nonneg (hp.1 i) (Real.exp_pos _).le)).mpr
    ⟨i, Finset.mem_univ _, mul_pos hi (Real.exp_pos _)⟩

@[simp] theorem partition_zero {ι : Type uι} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) : partition p a 0 = 1 := by
  simpa only [partition, zero_mul, Real.exp_zero, mul_one] using hp.2

theorem tiltedLaw_mem_simplex {ι : Type uι} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (t : ℝ) :
    tiltedLaw p a t ∈ probabilitySimplex ι := by
  refine ⟨fun i => div_nonneg (mul_nonneg (hp.1 i) (Real.exp_pos _).le)
    (partition_pos hp a t).le, ?_⟩
  simp only [tiltedLaw, ← Finset.sum_div]
  exact div_self (partition_pos hp a t).ne'

theorem entropy_partition_bound {ι : Type uι} [Fintype ι] {p q : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (hq : q ∈ probabilitySimplex ι)
    (hsupp : ∀ i, p i = 0 → q i = 0) (a : ι → ℝ) (t : ℝ) :
    entropy q ≤ Real.log (partition p a t) - ∑ i, q i*Real.log (p i) -
      t * ∑ i, q i*a i := by
  have hlog : ∀ i, q i * Real.log (tiltedLaw p a t i) =
      q i * Real.log (p i) + t*(q i*a i) - q i*Real.log (partition p a t) := by
    intro i
    by_cases hi : p i = 0
    · simp [hsupp i hi]
    · rw [tiltedLaw, Real.log_div (mul_ne_zero hi (Real.exp_ne_zero _))
        (partition_pos hp a t).ne', Real.log_mul hi (Real.exp_ne_zero _), Real.log_exp]
      ring
  calc
    entropy q ≤ -∑ i, q i*Real.log (tiltedLaw p a t i) :=
      entropy_le_crossEntropy (tiltedLaw_mem_simplex hp a t) hq (by
        intro i hi
        have hii : p i = 0 := by
          have := (div_eq_zero_iff).mp hi
          rcases this with hh | hh
          · exact (mul_eq_zero.mp hh).resolve_right (Real.exp_ne_zero _)
          · exact ((partition_pos hp a t).ne' hh).elim
        exact hsupp i hii)
    _ = _ := by
      simp_rw [hlog]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul, hq.2, one_mul]
      ring

def linearScore (G : LooplessGraph V E) (u : E → ℝ) (c : ℝ) (M : G.Matching) : ℝ :=
  (∑ e, u e * G.indicator M e) - c

omit [Fintype V] [DecidableEq V] in
theorem sum_mean_assoc (G : LooplessGraph V E) (p : G.Matching → ℝ) (u : E → ℝ) :
    (∑ M, p M * (∑ e, u e * G.indicator M e)) = ∑ e, u e * G.mean p e := by
  simp only [LooplessGraph.mean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro M _
  ring

omit [Fintype V] [DecidableEq V] in
theorem linearScore_expectation (G : LooplessGraph V E) (p : G.Matching → ℝ)
    (u : E → ℝ) (c : ℝ) :
    (∑ M, p M * linearScore G u c M) =
      (∑ e, u e * G.mean p e) - c * ∑ M, p M := by
  simp only [linearScore, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [sum_mean_assoc]
  ring

omit [Fintype V] [DecidableEq V] in

theorem matching_entropy_dual_bound (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y)
    {r : G.Matching → ℝ} (hr : r ∈ probabilitySimplex G.Matching)
    (hrsupport : ∀ M, p M = 0 → r M = 0)
    (u : E → ℝ) (c t : ℝ) :
    maxMatchingEntropy G (G.mean r) ≤
      Real.log (partition p (linearScore G u c) t) - ∑ M, r M * Real.log (p M) -
        t * ∑ M, r M * linearScore G u c M := by
  obtain ⟨q, hq, heq⟩ := maxMatchingEntropy_attained G (G.mean_mem_polytope hr)
  have hsuppq := matching_optimizer_face_support G hp hopt hq.1 hr hq.2 hrsupport
  have hmean : G.mean (q-r) = 0 := by
    change G.meanLinear (q-r) = 0
    rw [map_sub]
    change G.mean q-G.mean r = 0
    rw [hq.2, sub_self]
  have hsum : ∑ M, (q-r) M = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hq.1.2, hr.2, sub_self]
  have hlog := matching_optimizer_log_annihilates G hp hopt (q-r) hsum hmean
    (fun M hM => by simp [hsuppq M hM, hrsupport M hM])
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] at hlog
  have hscore : (∑ M, q M*linearScore G u c M) = ∑ M, r M*linearScore G u c M := by
    rw [linearScore_expectation, linearScore_expectation, hq.2, hq.1.2, hr.2]
  rw [← heq]
  simpa only [hlog, hscore] using entropy_partition_bound hp.1 hq.1 hsuppq
    (linearScore G u c) t

theorem partition_hasDerivAt {ι : Type uι} [Fintype ι] (p a : ι → ℝ) (t : ℝ) :
    HasDerivAt (partition p a) (partition (fun i => p i*a i) a t) t := by
  apply HasDerivAt.fun_sum
  intro i _
  simpa only [one_mul, id_eq, mul_assoc, mul_comm, mul_left_comm] using
    (((hasDerivAt_id t).mul_const (a i)).exp.const_mul (p i))

theorem logPartition_hasDerivAt {ι : Type uι} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => Real.log (partition p a t))
      (partition (fun i => p i*a i) a t / partition p a t) t :=
  (partition_hasDerivAt p a t).log (partition_pos hp a t).ne'

theorem logPartition_second {ι : Type uι} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) :
    HasDerivAt (fun t => partition (fun i => p i*a i) a t / partition p a t)
      ((∑ i, p i*(a i)^2) - (∑ i, p i*a i)^2) 0 := by
  have hd := (partition_hasDerivAt (fun i => p i*a i) a 0).div
    (partition_hasDerivAt p a 0) (partition_pos hp a 0).ne'
  refine hd.congr_deriv ?_
  simp only [partition, zero_mul, Real.exp_zero, mul_one, hp.2, one_pow, div_one]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

end MatchingEntropyBounds

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def entropyLineD {ι : Type uι} [Fintype ι] (x v : ι → ℝ) (t : ℝ) : ℝ :=
  -∑ i, v i * Real.log (x i+t*v i) - ∑ i, v i

theorem entropy_line_hasDerivAt_at {ι : Type uι} [Fintype ι] (x v : ι → ℝ)
    (t : ℝ) (h : ∀ i, x i+t*v i ≠ 0 ∨ v i = 0) :
    HasDerivAt (fun t : ℝ => entropy (fun i => x i+t*v i)) (entropyLineD x v t) t := by
  have hd : ∀ i, HasDerivAt (fun t : ℝ => Real.negMulLog (x i+t*v i))
      ((-Real.log (x i+t*v i)-1)*v i) t := by
    intro i
    rcases h i with hi | hi
    · simpa only [one_mul, Function.comp_def, id_eq] using
        (Real.hasDerivAt_negMulLog hi).comp t
          (((hasDerivAt_id t).mul_const (v i)).const_add (x i))
    · simpa only [hi, mul_zero, add_zero] using (hasDerivAt_const t (Real.negMulLog (x i)))
  have he : (∑ i, (-Real.log (x i+t*v i)-1)*v i) = entropyLineD x v t := by
    simp_rw [sub_mul, one_mul, neg_mul, mul_comm (Real.log (x _+t*v _))]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    rfl
  rw [← he]
  simpa only [entropy, Finset.sum_apply] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i))

theorem entropy_line_deriv_eventually {ι : Type uι} [Fintype ι] (x v : ι → ℝ)
    (hsupp : ∀ i, x i = 0 → v i = 0) :
    deriv (fun t : ℝ => entropy (fun i => x i+t*v i)) =ᶠ[𝓝 0] entropyLineD x v := by
  have hh : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, x i+t*v i ≠ 0 ∨ v i = 0 := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : x i = 0
    · exact Filter.Eventually.of_forall (fun t => Or.inr (hsupp i hi))
    · have hc : ContinuousAt (fun t : ℝ => x i+t*v i) 0 := by fun_prop
      have hn := hc.eventually_ne (show x i+(0:ℝ)*v i ≠ 0 by simpa using hi)
      exact hn.mono (fun t ht => Or.inl ht)
  filter_upwards [hh] with t ht
  exact (entropy_line_hasDerivAt_at x v t ht).deriv

theorem entropyLineD_hasDerivAt {ι : Type uι} [Fintype ι] (x v : ι → ℝ)
    (hsupp : ∀ i, x i = 0 → v i = 0) :
    HasDerivAt (entropyLineD x v) (-∑ i, (v i)^2/x i) 0 := by
  have hd : ∀ i, HasDerivAt (fun t : ℝ => v i*Real.log (x i+t*v i))
      ((v i)^2/x i) 0 := by
    intro i
    by_cases hi : x i = 0
    · simpa only [hi, hsupp i hi, zero_mul, zero_pow (by omega : 2 ≠ 0), zero_div] using
        (hasDerivAt_const (0:ℝ) (0:ℝ))
    · have hh := ((((hasDerivAt_id (0:ℝ)).mul_const (v i)).const_add (x i)).log
          (by simpa using hi)).const_mul (v i)
      simpa only [id_eq, one_mul, zero_mul, add_zero, pow_two, mul_div_assoc] using hh
  change HasDerivAt (fun t : ℝ => -(∑ i, v i*Real.log (x i+t*v i)) - ∑ i, v i)
    (-∑ i, (v i)^2/x i) 0
  exact (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i)).neg.sub_const (∑ i, v i)

theorem entropy_line_second {ι : Type uι} [Fintype ι] (x v : ι → ℝ)
    (hsupp : ∀ i, x i = 0 → v i = 0) :
    HasDerivAt (deriv (fun t : ℝ => entropy (fun i => x i+t*v i)))
      (-∑ i, (v i)^2/x i) 0 :=
  (entropyLineD_hasDerivAt x v hsupp).congr_of_eventuallyEq
    (entropy_line_deriv_eventually x v hsupp)

theorem second_deriv_quadratic_adjustment {f fD g gD : ℝ → ℝ} {fDD gDD c₀ c₁ v : ℝ}
    (hf : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt f (fD t) t)
    (hg : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt g (gD t) t)
    (hfD : HasDerivAt fD fDD 0) (hgD : HasDerivAt gD gDD 0) :
    HasDerivAt (deriv (fun t => f t+c₀+t*c₁+t^2*v-g t))
      (fDD+2*v-gDD) 0 := by
  have hfirst : deriv (fun t => f t+c₀+t*c₁+t^2*v-g t) =ᶠ[𝓝 (0:ℝ)]
      (fun t => fD t+c₁+2*t*v-gD t) := by
    filter_upwards [hf, hg] with t hft hgt
    have hd := (((hft.add_const c₀).fun_add ((hasDerivAt_id t).mul_const c₁)).fun_add
      (((hasDerivAt_id t).fun_pow 2).mul_const v)).fun_sub hgt
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq, one_mul,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using hd.deriv
  have hd := ((hfD.add_const c₁).fun_add
    (((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const v)).fun_sub hgD
  have hd' : HasDerivAt (fun t => fD t+c₁+2*t*v-gD t) (fDD+2*v-gDD) 0 := by
    simpa only [Pi.add_apply, Pi.sub_apply, id_eq, mul_one] using hd
  exact hd'.congr_of_eventuallyEq hfirst

theorem second_deriv_nonpos_of_local_max {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra h
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge h
  have hmin := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hm, hmin] with y h₁ h₂
    exact le_antisymm h₁ h₂
  have hh := he.deriv.deriv_eq
  simp only [deriv_const', deriv_const] at hh
  linarith

theorem entropy_line_eventually_hasDerivAt {ι : Type uι} [Fintype ι] (x v : ι → ℝ)
    (hsupp : ∀ i, x i = 0 → v i = 0) :
    ∀ᶠ t : ℝ in 𝓝 0,
      HasDerivAt (fun t : ℝ => entropy (fun i => x i+t*v i)) (entropyLineD x v t) t := by
  have hh : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, x i+t*v i ≠ 0 ∨ v i = 0 := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : x i = 0
    · exact Filter.Eventually.of_forall (fun t => Or.inr (hsupp i hi))
    · have hc : ContinuousAt (fun t : ℝ => x i+t*v i) 0 := by fun_prop
      have hn := hc.eventually_ne (show x i+(0:ℝ)*v i ≠ 0 by simpa using hi)
      exact hn.mono (fun t ht => Or.inl ht)
  exact hh.mono (fun t ht => entropy_line_hasDerivAt_at x v t ht)

theorem score_law_eventually_simplex {ι : Type uι} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (hcenter : ∑ i, p i*a i = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, (fun i => p i+t*(p i*a i)) ∈ probabilitySimplex ι := by
  have hh : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 < 1+t*a i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : Continuous (fun t : ℝ => 1+t*a i) := by fun_prop
    exact (isOpen_lt continuous_const hc).mem_nhds (by norm_num)
  filter_upwards [hh] with t ht
  constructor
  · intro i
    have h := mul_nonneg (hp.1 i) (ht i).le
    nlinarith
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp.2, hcenter]
    ring

omit [Fintype V] [DecidableEq V] in
theorem mean_score_support (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) (a : G.Matching → ℝ) :
    ∀ e, G.mean p e = 0 → G.mean (fun M => p M*a M) e = 0 := by
  intro e he
  have hterms : ∀ M, p M*G.indicator M e = 0 := by
    have hh := (Finset.sum_eq_zero_iff_of_nonneg
      (fun M (_ : M ∈ Finset.univ) => mul_nonneg (hp.1 M) (G.indicator_nonneg M e))).mp he
    exact fun M => hh M (Finset.mem_univ M)
  apply Finset.sum_eq_zero
  intro M _
  calc
    _ = a M*(p M*G.indicator M e) := by ring
    _ = 0 := by rw [hterms, mul_zero]

end MatchingEntropyBounds

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

open Matrix

variable {A : Type uA} {I : Type uI} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]

def weightedColumns (p : A → ℝ) (b : A → I → ℝ) : Matrix I A ℝ :=
  fun i a => Real.sqrt (p a) * b a i

def covariance (p : A → ℝ) (b : A → I → ℝ) : Matrix I I ℝ :=
  weightedColumns p b * (weightedColumns p b)ᵀ

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_posSemidef (p : A → ℝ) (b : A → I → ℝ) :
    (covariance p b).PosSemidef := by
  simpa only [covariance, conjTranspose_eq_transpose_of_trivial] using
    posSemidef_self_mul_conjTranspose (weightedColumns p b)

omit [Fintype I] [DecidableEq A] [DecidableEq I] in
theorem covariance_entry {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ) (i j : I) :
    covariance p b i j = ∑ a, p a*b a i*b a j := by
  unfold covariance
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp only [weightedColumns, Matrix.transpose_apply]
  calc
    _ = (Real.sqrt (p a))^2 * b a i * b a j := by ring
    _ = _ := by rw [Real.sq_sqrt (hp a)]

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_mulVec {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ)
    (u : I → ℝ) (i : I) :
    (covariance p b *ᵥ u) i = ∑ a, p a*b a i*(b a ⬝ᵥ u) := by
  simp only [Matrix.mulVec, dotProduct, covariance_entry hp, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_quadratic {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ)
    (u : I → ℝ) : u ⬝ᵥ (covariance p b *ᵥ u) = ∑ a, p a*(b a ⬝ᵥ u)^2 := by
  rw [dotProduct]
  simp_rw [covariance_mulVec hp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (∑ i, u i*(p a*b a i*(b a ⬝ᵥ u))) =
      (∑ i, b a i*u i)*(p a*(b a ⬝ᵥ u)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = p a*(b a ⬝ᵥ u)^2 := by rw [← dotProduct]; ring

def weightedDirectionSpace (p : A → ℝ) (b : A → I → ℝ) : Submodule ℝ (I → ℝ) :=
  Submodule.span ℝ (Set.range fun a : {a // 0 < p a} => b a.val)

omit [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I] in
theorem weightedColumns_span {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ) :
    Submodule.span ℝ (Set.range (weightedColumns p b).col) = weightedDirectionSpace p b := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    by_cases ha : 0 < p a
    · have hb : b a ∈ weightedDirectionSpace p b := Submodule.subset_span ⟨⟨a,ha⟩,rfl⟩
      exact Submodule.smul_mem _ (Real.sqrt (p a)) hb
    · have hz := le_antisymm (le_of_not_gt ha) (hp a)
      have he : (weightedColumns p b).col a = 0 := by
        ext i
        simp [weightedColumns, Matrix.col, hz]
      rw [he]
      exact (weightedDirectionSpace p b).zero_mem
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    have hb : (weightedColumns p b).col a.val ∈
        Submodule.span ℝ (Set.range (weightedColumns p b).col) := Submodule.subset_span ⟨a.val,rfl⟩
    have hs : Real.sqrt (p a.val) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 a.property)
    have hh := Submodule.smul_mem _ (Real.sqrt (p a.val))⁻¹ hb
    have he : (Real.sqrt (p a.val))⁻¹ • (weightedColumns p b).col a.val = b a.val := by
      ext i
      change (Real.sqrt (p a.val))⁻¹ * (Real.sqrt (p a.val) * b a.val i) = _
      rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
    rw [he] at hh
    exact hh

omit [DecidableEq A] [DecidableEq I] in
theorem covariance_rank {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (b : A → I → ℝ) :
    (covariance p b).rank = Module.finrank ℝ (weightedDirectionSpace p b) := by
  rw [covariance, rank_self_mul_transpose, rank_eq_finrank_span_cols, weightedColumns_span hp]

def normalizedCentered (v : A → I → ℝ) (x : I → ℝ) (a : A) (i : I) : ℝ :=
  (v a i-x i)/Real.sqrt (x i)

omit [Fintype I] [DecidableEq A] [DecidableEq I] in
theorem normalizedCentered_mean {p : A → ℝ} (hp : ∑ a, p a = 1)
    (v : A → I → ℝ) (x : I → ℝ) (hx : ∀ i, ∑ a, p a*v a i = x i) (i : I) :
    ∑ a, p a*normalizedCentered v x a i = 0 := by
  simp only [normalizedCentered, ← mul_div_assoc, mul_sub, ← Finset.sum_div,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul, hx, sub_self, zero_div]

omit [Fintype I] [DecidableEq A] [DecidableEq I] in
theorem normalizedCentered_variance {p : A → ℝ} (hp : ∑ a, p a = 1)
    (v : A → I → ℝ) (hv : ∀ a i, (v a i)^2=v a i) (x : I → ℝ)
    (hx : ∀ i, ∑ a, p a*v a i = x i) (hxp : ∀ i, 0 < x i) (i : I) :
    ∑ a, p a*(normalizedCentered v x a i)^2 = 1-x i := by
  have heq : ∀ a, p a*(normalizedCentered v x a i)^2 =
      (p a*v a i-2*x i*(p a*v a i)+(x i)^2*p a)/x i := by
    intro a
    rw [normalizedCentered, div_pow, Real.sq_sqrt (hxp i).le, ← mul_div_assoc]
    congr 1
    calc
      _ = p a*(v a i)^2-2*x i*(p a*v a i)+(x i)^2*p a := by ring
      _ = _ := by rw [hv]
  simp_rw [heq]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hx, hp, mul_one]
  field_simp [ne_of_gt (hxp i)]
  ring

omit [DecidableEq A] [DecidableEq I] in
theorem normalized_covariance_trace {p : A → ℝ} (hp : p ∈ probabilitySimplex A)
    (v : A → I → ℝ) (hv : ∀ a i, (v a i)^2=v a i) (x : I → ℝ)
    (hx : ∀ i, ∑ a, p a*v a i = x i) (hxp : ∀ i, 0 < x i) :
    (covariance p (normalizedCentered v x)).trace = Fintype.card I - ∑ i, x i := by
  unfold Matrix.trace Matrix.diag
  simp_rw [covariance_entry hp.1]
  have heq : ∀ i, (∑ a, p a*normalizedCentered v x a i*normalizedCentered v x a i) = 1-x i := by
    intro i
    simpa only [pow_two, mul_assoc] using
      normalizedCentered_variance hp.2 v hv x hx hxp i
  simp_rw [heq]
  simp

end MatchingEntropyBounds

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter Matrix


namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in

theorem maxMatchingEntropy_mix_ge (G : LooplessGraph V E) {x y : E → ℝ}
    (hx : x ∈ G.polytope) (hy : y ∈ G.polytope) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1-t)*maxMatchingEntropy G x+t*maxMatchingEntropy G y ≤
      maxMatchingEntropy G ((1-t) • x+t • y) := by
  obtain ⟨p,hp,hpe⟩ := maxMatchingEntropy_attained G hx
  obtain ⟨q,hq,hqe⟩ := maxMatchingEntropy_attained G hy
  rw [← hpe,← hqe]
  apply (entropy_mix_ge hp.1.1 hq.1.1 ht).trans
  apply entropy_le_maxMatchingEntropy
  refine ⟨convex_probabilitySimplex _ hp.1 hq.1 (sub_nonneg.mpr ht.2) ht.1 (by ring),?_⟩
  change G.meanLinear ((1-t) • p+t • q) = _
  rw [map_add,map_smul,map_smul]
  change (1-t) • G.mean p+t • G.mean q = _
  rw [hp.2,hq.2]

theorem maxMatchingEntropy_lowerSemicontinuousOn (G : LooplessGraph V E)
    (heven : Even (Fintype.card V)) :
    LowerSemicontinuousOn (maxMatchingEntropy G) G.polytope := by
  intro x hx r hr
  have hn := maxMatchingEntropy_nonneg G hx
  have hden : 0 < maxMatchingEntropy G x+1 := by linarith
  have ha : 0 < min (1:ℝ) ((maxMatchingEntropy G x-r)/(maxMatchingEntropy G x+1)) :=
    lt_min (by norm_num) (div_pos (sub_pos.mpr hr) hden)
  obtain ⟨t,ht0,htt⟩ := exists_between ha
  have ht1 : t<1 := htt.trans_le (min_le_left _ _)
  have htb : t*(maxMatchingEntropy G x+1) < maxMatchingEntropy G x-r :=
    (lt_div_iff₀ hden).mp (htt.trans_le (min_le_right _ _))
  filter_upwards [G.polytope_eventually_expand heven hx ht0] with y hy
  have hh := maxMatchingEntropy_mix_ge G hx hy ⟨ht0.le,ht1.le⟩
  have he : (1-t) • x+t • (x+t⁻¹ • (y-x))=y := by
    ext e
    simp only [Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
    field_simp
    ring
  rw [he] at hh
  have hz := mul_nonneg ht0.le (maxMatchingEntropy_nonneg G hy)
  nlinarith

end MatchingEntropyBounds

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter Matrix


namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def matchingNormalized (G : LooplessGraph V E) (x : E → ℝ) :
    G.Matching → {e // 0 < x e} → ℝ :=
  normalizedCentered (fun M e => G.indicator M e.val) (fun e => x e.val)

omit [Fintype V] [DecidableEq V] in
theorem matchingNormalized_average (G : LooplessGraph V E) {x y : E → ℝ}
    {q : G.Matching → ℝ} (hq : q ∈ G.feasibleLaws y) (e : {e // 0 < x e}) :
    (∑ M, q M*matchingNormalized G x M e)=(y e.val-x e.val)/Real.sqrt (x e.val) := by
  simp only [matchingNormalized,normalizedCentered,← mul_div_assoc,mul_sub,
    ← Finset.sum_div,Finset.sum_sub_distrib,← Finset.sum_mul,hq.1.2,one_mul]
  rw [show (∑ M, q M*G.indicator M e.val)=y e.val from congrFun hq.2 e.val]

omit [Fintype V] [DecidableEq V] in

theorem midpoint_law_support (G : LooplessGraph V E) {x v : E → ℝ} {a : ℝ}
    {p q r : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x)
    (hq : q ∈ G.feasibleLaws (x+a • v))
    (hr : r ∈ G.feasibleLaws (x+(-a) • v)) :
    ∀ M, 0 < q M → 0 < p M := by
  let w : G.Matching → ℝ := (1/2:ℝ) • q+(1/2:ℝ) • r
  have hw : w ∈ G.feasibleLaws x := by
    refine ⟨convex_probabilitySimplex _ hq.1 hr.1 (by norm_num) (by norm_num) (by norm_num),?_⟩
    change G.meanLinear ((1/2:ℝ) • q+(1/2:ℝ) • r) = _
    rw [map_add,map_smul,map_smul]
    change (1/2:ℝ) • G.mean q+(1/2:ℝ) • G.mean r = _
    rw [hq.2,hr.2]
    ext e
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  intro M hM
  apply matching_optimizer_support G hp hw hopt
  change 0 < (1/2:ℝ)*q M+(1/2:ℝ)*r M
  have hh := hr.1.1 M
  linarith

theorem normalized_face_mem (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) {p : G.Matching → ℝ}
    (hp : p ∈ G.feasibleLaws x) (hopt : entropy p=maxMatchingEntropy G x)
    {u : {e // 0 < x e} → ℝ} (hu : u ∈ G.faceSpace x) :
    (fun e => u e/Real.sqrt (x e.val)) ∈ weightedDirectionSpace p (matchingNormalized G x) := by
  have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p,hp⟩
  have hev := G.faceSpace_eventually_line (G.polytope_subset_constraintPolytope hx) hu
  have hneg : ∀ᶠ t : ℝ in 𝓝 0, x+(-t) • LooplessGraph.positiveExtension x u ∈ G.constraintPolytope := by
    have hc : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by simpa using continuous_neg.tendsto (0:ℝ)
    exact hc.eventually hev
  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (x+t • LooplessGraph.positiveExtension x u ∈ G.constraintPolytope ∧
      x+(-t) • LooplessGraph.positiveExtension x u ∈ G.constraintPolytope) ∧ 0 < t :=
    ((hev.and hneg).filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  obtain ⟨a,⟨ha,hna⟩,ha0⟩ := hh.exists
  rw [← G.polytope_eq_constraints heven] at ha hna
  obtain ⟨q,hq⟩ := (G.mem_polytope_iff _).mp ha
  obtain ⟨r,hr⟩ := (G.mem_polytope_iff _).mp hna
  have hsupp := midpoint_law_support G hp hopt hq hr
  have hsum : (∑ M, q M • matchingNormalized G x M) ∈
      weightedDirectionSpace p (matchingNormalized G x) := by
    apply Submodule.sum_mem
    intro M _
    by_cases hM : 0 < p M
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨M,hM⟩,rfl⟩)
    · have hq0 : q M=0 := le_antisymm (le_of_not_gt fun hqM => hM (hsupp M hqM)) (hq.1.1 M)
      simp only [hq0,zero_smul]
      exact Submodule.zero_mem _
  have hin := Submodule.smul_mem _ a⁻¹ hsum
  have he : a⁻¹ • (∑ M, q M • matchingNormalized G x M) =
      (fun e => u e/Real.sqrt (x e.val)) := by
    ext e
    simp only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
    rw [matchingNormalized_average G hq]
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,LooplessGraph.positiveExtension_pos]
    field_simp
    ring
  rwa [he] at hin

def normalizeLinear (x : E → ℝ) :
    ({e // 0 < x e} → ℝ) →ₗ[ℝ] ({e // 0 < x e} → ℝ) where
  toFun := fun u e => u e/Real.sqrt (x e.val)
  map_add' := by intro u v; ext e; exact add_div _ _ _
  map_smul' := by intro a u; ext e; exact mul_div_assoc _ _ _

omit [DecidableEq E] in
theorem sum_positive_support (x f : E → ℝ) (hf : ∀ e, ¬ 0 < x e → f e=0) :
    (∑ e, f e) = ∑ e : {e // 0 < x e}, f e.val := by
  classical
  have hz : (∑ e : {e // ¬ 0 < x e}, f e.val)=0 :=
    Finset.sum_eq_zero fun e _ => hf e.val e.property
  have hh := Fintype.sum_subtype_add_sum_subtype (fun e => 0 < x e) f
  rw [hz,add_zero] at hh
  exact hh.symm

def matchingScoreWeights (x : E → ℝ) (u : {e // 0 < x e} → ℝ) : E → ℝ :=
  LooplessGraph.positiveExtension x (fun e => u e/Real.sqrt (x e.val))

omit [Fintype V] [DecidableEq V] in
theorem matchingNormalized_score (G : LooplessGraph V E) (x : E → ℝ)
    (u : {e // 0 < x e} → ℝ) (M : G.Matching) :
    linearScore G (matchingScoreWeights x u) (∑ e, matchingScoreWeights x u e*x e) M =
      matchingNormalized G x M ⬝ᵥ u := by
  classical
  unfold linearScore
  rw [← Finset.sum_sub_distrib]
  rw [sum_positive_support x _ (fun e he => by simp [matchingScoreWeights,LooplessGraph.positiveExtension,he])]
  rw [dotProduct]
  apply Finset.sum_congr rfl
  intro e _
  simp only [matchingScoreWeights,LooplessGraph.positiveExtension_pos,matchingNormalized,normalizedCentered]
  ring

omit [Fintype V] [DecidableEq V] in
theorem matchingNormalized_mulVec (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (u : {e // 0 < x e} → ℝ) (e : {e // 0 < x e}) :
    (covariance p (matchingNormalized G x) *ᵥ u) e =
      G.mean (fun M => p M * linearScore G (matchingScoreWeights x u)
        (∑ e, matchingScoreWeights x u e*x e) M) e.val / Real.sqrt (x e.val) := by
  let a := linearScore G (matchingScoreWeights x u) (∑ e, matchingScoreWeights x u e*x e)
  have hcenter : ∑ M, p M*a M=0 := by
    dsimp only [a]
    rw [linearScore_expectation,hp.2,hp.1.2,mul_one,sub_self]
  calc
    _ = ∑ M, (p M*a M*G.indicator M e.val-x e.val*(p M*a M))/Real.sqrt (x e.val) := by
      rw [covariance_mulVec hp.1.1]
      apply Finset.sum_congr rfl
      intro M _
      rw [← matchingNormalized_score G x u M]
      change p M*((G.indicator M e.val-x e.val)/Real.sqrt (x e.val))*a M = _
      ring
    _ = _ := by
      rw [← Finset.sum_div,Finset.sum_sub_distrib,← Finset.mul_sum,hcenter,mul_zero,sub_zero]
      rfl

end MatchingEntropyBounds

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def binaryEntropy (x : E → ℝ) : ℝ := entropy x + entropy (fun e => 1 - x e)

def separableLower (x : E → ℝ) : ℝ := entropy x - 3 * entropy (fun e => 1 - x e)

def structuralBase (k : ℕ) : ℝ :=
  if k = 1 then 1 else (k : ℝ) * (1 - 1 / (k : ℝ)) ^ (3 * (k - 1))

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem continuous_separableLower : Continuous (separableLower (E := E)) := by
  exact continuous_entropy.sub (continuous_const.mul (continuous_entropy.comp (by fun_prop)))

def separableLineD (x v : E → ℝ) (t : ℝ) : ℝ :=
  entropyLineD x v t - 3 * entropyLineD (fun e => 1-x e) (fun e => -v e) t

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem separable_line_eventually_hasDerivAt (x v : E → ℝ)
    (hzero : ∀ e, x e = 0 → v e = 0) (hone : ∀ e, x e = 1 → v e = 0) :
    ∀ᶠ t : ℝ in 𝓝 0,
      HasDerivAt (fun t => separableLower (fun e => x e+t*v e))
        (separableLineD x v t) t := by
  have hbar : ∀ e, 1-x e=0 → -v e=0 := by
    intro e he
    rw [hone e (by linarith), neg_zero]
  filter_upwards [entropy_line_eventually_hasDerivAt x v hzero,
    entropy_line_eventually_hasDerivAt (fun e => 1-x e) (fun e => -v e) hbar]
    with t ht hb
  have he : (fun t => separableLower (fun e => x e+t*v e)) =
      (fun t => entropy (fun e => x e+t*v e) -
        3 * entropy (fun e => (1-x e)+t*(-v e))) := by
    funext t
    unfold separableLower
    congr 2
    congr 1
    funext e
    ring
  rw [he]
  exact ht.sub (hb.const_mul 3)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem separableLineD_hasDerivAt (x v : E → ℝ)
    (hzero : ∀ e, x e = 0 → v e = 0) (hone : ∀ e, x e = 1 → v e = 0) :
    HasDerivAt (separableLineD x v)
      (-(∑ e, (v e)^2/x e) + 3*(∑ e, (v e)^2/(1-x e))) 0 := by
  have hbar : ∀ e, 1-x e=0 → -v e=0 := by
    intro e he
    rw [hone e (by linarith), neg_zero]
  have hd := (entropyLineD_hasDerivAt x v hzero).sub
    ((entropyLineD_hasDerivAt (fun e => 1-x e) (fun e => -v e) hbar).const_mul 3)
  exact hd.congr_deriv (by simp only [neg_sq]; ring)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem separable_second_variation {A : Type uA} [Fintype A]
    (x v : E → ℝ) (hzero : ∀ e, x e=0 → v e=0) (hone : ∀ e, x e=1 → v e=0)
    {p : A → ℝ} (hp : p ∈ probabilitySimplex A) (a : A → ℝ)
    (hcenter : ∑ i, p i*a i=0) (c₀ c₁ : ℝ)
    (hlocal : IsLocalMax (fun t => separableLower (fun e => x e+t*v e) +
      c₀+t*c₁+t^2*(∑ i, p i*(a i)^2)-Real.log (partition p a t)) 0) :
    -(∑ e, (v e)^2/x e) + 3*(∑ e, (v e)^2/(1-x e)) +
      (∑ i, p i*(a i)^2) ≤ 0 := by
  have hf := separable_line_eventually_hasDerivAt x v hzero hone
  have hg : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt (fun t => Real.log (partition p a t))
      (partition (fun i => p i*a i) a t / partition p a t) t :=
    Filter.Eventually.of_forall (logPartition_hasDerivAt hp a)
  have hd := second_deriv_quadratic_adjustment (c₀ := c₀) (c₁ := c₁)
    (v := ∑ i, p i*(a i)^2) hf hg (separableLineD_hasDerivAt x v hzero hone)
    (logPartition_second hp a)
  have hc : ContinuousAt (fun t => separableLower (fun e => x e+t*v e) +
      c₀+t*c₁+t^2*(∑ i, p i*(a i)^2)-Real.log (partition p a t)) 0 := by
    apply ContinuousAt.sub
    · apply ContinuousAt.add
      · apply ContinuousAt.add
        · exact hf.self_of_nhds.continuousAt.add_const c₀
        · fun_prop
      · fun_prop
    · exact hg.self_of_nhds.continuousAt
  have hh := second_deriv_nonpos_of_local_max hlocal hc
  rw [hd.deriv, hcenter] at hh
  nlinarith

omit [Fintype V] [DecidableEq V] in
theorem mean_score_one (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) (a : G.Matching → ℝ)
    (hcenter : ∑ M, p M*a M=0) :
    ∀ e, G.mean p e=1 → G.mean (fun M => p M*a M) e=0 := by
  intro e he
  have hz : ∑ M, p M*(1-G.indicator M e)=0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hp.2]
    change 1-G.mean p e=0
    rw [he, sub_self]
  have hterms : ∀ M, p M*(1-G.indicator M e)=0 := by
    exact fun M => (Finset.sum_eq_zero_iff_of_nonneg
      (fun M (_ : M ∈ Finset.univ) =>
        mul_nonneg (hp.1 M) (sub_nonneg.mpr (G.indicator_le_one M e)))).mp hz M (by simp)
  calc
    _ = ∑ M, p M*a M := by
      apply Finset.sum_congr rfl
      intro M _
      have hh := hterms M
      have hh' : a M*(p M*(1-G.indicator M e))=0 := by rw [hh, mul_zero]
      nlinarith [hh']
    _ = 0 := hcenter

omit [Fintype V] [DecidableEq V] in

theorem matching_separable_second_variation (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x)
    (hmax : ∀ y ∈ G.polytope, separableLower y-maxMatchingEntropy G y ≤
      separableLower x-maxMatchingEntropy G x)
    (u : E → ℝ) (c : ℝ) (hcenter : ∑ M, p M*linearScore G u c M=0) :
    -(∑ e, (G.mean (fun M => p M*linearScore G u c M) e)^2/x e) +
      3*(∑ e, (G.mean (fun M => p M*linearScore G u c M) e)^2/(1-x e)) +
      (∑ M, p M*(linearScore G u c M)^2) ≤ 0 := by
  let a := linearScore G u c
  let v := G.mean (fun M => p M*a M)
  let c₀ := ∑ M, p M*Real.log (p M)
  let c₁ := ∑ M, (p M*a M)*Real.log (p M)
  have hzero : ∀ e, x e=0 → v e=0 := by
    rw [← hp.2]
    exact mean_score_support G hp.1 a
  have hone : ∀ e, x e=1 → v e=0 := by
    rw [← hp.2]
    exact mean_score_one G hp.1 a hcenter
  apply separable_second_variation x v hzero hone hp.1 a hcenter c₀ c₁
  filter_upwards [score_law_eventually_simplex hp.1 a hcenter] with t ht
  let r := fun M => p M+t*(p M*a M)
  have hr : r ∈ probabilitySimplex G.Matching := ht
  have hrmean : G.mean r=fun e => x e+t*v e := by
    change G.meanLinear (p+t • (fun M => p M*a M)) = _
    rw [map_add, map_smul]
    change G.mean p+t • v = _
    rw [hp.2]
    rfl
  have hdual := matching_entropy_dual_bound G hp hopt hr
    (fun M hM => by dsimp [r]; simp [hM]) u c t
  have hscore : (∑ M, r M*a M)=t*(∑ M, p M*(a M)^2) := by
    dsimp [r]
    simp_rw [add_mul, mul_assoc t, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hcenter, zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro M _
    ring
  have hlog : (∑ M, r M*Real.log (p M))=c₀+t*c₁ := by
    dsimp [r, c₀, c₁]
    simp_rw [add_mul, mul_assoc t, Finset.sum_add_distrib, ← Finset.mul_sum]
  change maxMatchingEntropy G (G.mean r) ≤
    Real.log (partition p a t) - (∑ M, r M*Real.log (p M)) - t*(∑ M, r M*a M) at hdual
  rw [hlog, hscore] at hdual
  have hmaxr := hmax (G.mean r) (G.mean_mem_polytope hr)
  have hpart := partition_zero hp.1 a
  simp only [zero_mul, zero_pow (by omega : 2 ≠ 0), add_zero, hpart,
    Real.log_one, sub_zero]
  rw [← hopt, entropy_eq p] at hmaxr
  rw [← hrmean]
  dsimp only [c₀] at *
  nlinarith

end MatchingEntropyBounds

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Matrix


namespace MatchingEntropyBounds

theorem spectral_diagonal {I : Type uI} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℝ} (hC : C.IsHermitian) (e : I) :
    C e e = ∑ i, hC.eigenvalues i * (hC.eigenvectorBasis i e)^2 := by
  have hh := congrArg (fun A : Matrix I I ℝ => A e e) hC.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hh
  simpa only [mul_apply, diagonal_apply, star_eq_conjTranspose, conjTranspose_apply,
    star_trivial, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq,
    mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Matrix.IsHermitian.eigenvectorUnitary_apply, pow_two, mul_comm, mul_left_comm,
    mul_assoc] using hh

theorem covariance_weighted_rank {I : Type uI} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℝ} (hC : C.PosSemidef) (w : I → ℝ)
    (hsecond : ∀ u : I → ℝ,
      u ⬝ᵥ (C *ᵥ u) ≤ ∑ e, w e * ((C *ᵥ u) e)^2) :
    (C.rank : ℝ) ≤ ∑ e, w e * C e e := by
  let eig := hC.isHermitian.eigenvalues
  let b := hC.isHermitian.eigenvectorBasis
  have heig : ∀ i, 0 ≤ eig i := hC.eigenvalues_nonneg
  have hone : ∀ i, eig i ≠ 0 → 1 ≤ eig i * (∑ e, w e * (b i e)^2) := by
    intro i hi
    let v : I → ℝ := b i
    have hv : v ⬝ᵥ v=1 := by
      have hn := b.orthonormal.1 i
      have hb : inner ℝ (b i) (b i)=1 := by
        rw [real_inner_self_eq_norm_sq, hn]
        norm_num
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hb
    have he : C *ᵥ v=eig i • v := hC.isHermitian.mulVec_eigenvectorBasis i
    have hs := hsecond v
    rw [he] at hs
    simp only [dotProduct_smul, smul_eq_mul, hv, mul_one, Pi.smul_apply] at hs
    have heq : (∑ e, w e*(eig i * v e)^2) =
        (eig i)^2 * (∑ e, w e*(v e)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    rw [heq] at hs
    have hp : 0 < eig i := lt_of_le_of_ne (heig i) (Ne.symm hi)
    nlinarith
  rw [hC.isHermitian.rank_eq_card_non_zero_eigs]
  calc
    (Fintype.card {i // eig i ≠ 0} : ℝ) = ∑ i : {i // eig i ≠ 0}, (1:ℝ) := by simp
    _ ≤ ∑ i : {i // eig i ≠ 0}, eig i * (∑ e, w e*(b i e)^2) :=
      Finset.sum_le_sum fun i _ => hone i i.property
    _ = ∑ i, eig i * (∑ e, w e*(b i e)^2) := by
      exact sum_subtype_supported (fun i => eig i ≠ 0)
        (fun i => eig i * (∑ e, w e*(b i e)^2))
        (by intro i hi; rw [not_ne_iff.mp hi, zero_mul])
    _ = ∑ e, w e * C e e := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [spectral_diagonal hC.isHermitian e, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [eig, b]
      ring

end MatchingEntropyBounds

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Matrix Filter


namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem separableDefect_attains_max (G : LooplessGraph V E)
    (heven : Even (Fintype.card V)) (hPM : Nonempty G.Matching) :
    ∃ x ∈ G.polytope, ∀ y ∈ G.polytope,
      separableLower y-maxMatchingEntropy G y ≤ separableLower x-maxMatchingEntropy G x := by
  have hs : UpperSemicontinuousOn (fun y => separableLower y-maxMatchingEntropy G y)
      G.polytope := by
    simpa only [sub_eq_add_neg, Pi.neg_apply] using
      continuous_separableLower.continuousOn.upperSemicontinuousOn.add
        (maxMatchingEntropy_lowerSemicontinuousOn G heven).neg
  have hn : G.polytope.Nonempty := by
    obtain ⟨M⟩ := hPM
    exact ⟨G.indicator M,subset_convexHull ℝ _ (Set.mem_range_self M)⟩
  exact UpperSemicontinuousOn.exists_isMaxOn hn G.compact_polytope hs

theorem matching_covariance_rank_face (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) {p : G.Matching → ℝ}
    (hp : p ∈ G.feasibleLaws x) (hopt : entropy p=maxMatchingEntropy G x) :
    Fintype.card {e // 0 < x e} ≤ G.faceCodimension x+
      (covariance p (matchingNormalized G x)).rank := by
  let W := weightedDirectionSpace p (matchingNormalized G x)
  let L : G.faceSpace x →ₗ[ℝ] W :=
    ((normalizeLinear x).comp (G.faceSpace x).subtype).codRestrict W
      (fun u => normalized_face_mem G heven hp hopt u.property)
  have hi : Function.Injective L := by
    intro u v huv
    apply Subtype.ext
    funext e
    have hh := congrFun (congrArg Subtype.val huv) e
    change u.val e/Real.sqrt (x e.val)=v.val e/Real.sqrt (x e.val) at hh
    exact (div_left_inj' (ne_of_gt (Real.sqrt_pos.mpr e.property))).mp hh
  have hdim := LinearMap.finrank_le_finrank_of_injective hi
  have hq := (G.faceSpace x).finrank_quotient_add_finrank
  rw [covariance_rank hp.1.1]
  have hq' : G.faceCodimension x+Module.finrank ℝ (G.faceSpace x)=Fintype.card {e // 0 < x e} := by
    simpa only [LooplessGraph.faceCodimension,Module.finrank_pi,Module.finrank_self,Finset.sum_const,
      Finset.card_univ,smul_eq_mul,mul_one] using hq
  change Module.finrank ℝ (G.faceSpace x) ≤ Module.finrank ℝ W at hdim
  dsimp only [W] at hdim
  omega

theorem faceCodimension_strict (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hn : 0 < Fintype.card V) (hx : x ∈ G.polytope) :
    G.faceCodimension x < 2*Fintype.card V := by
  by_cases hn4 : 4 ≤ Fintype.card V
  · have hb := LooplessGraph.faceCodimension_strong_aux (Fintype.card V) G rfl heven hn4 x
      (G.polytope_subset_constraintPolytope hx)
    omega
  · have hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1 := by
      rintro ⟨S,_,hlo,hhi,_⟩
      have hh := Finset.card_compl_add_card S
      omega
    have hb := G.faceCodimension_no_tight heven hnt
    omega

omit [Fintype V] [DecidableEq V] in

theorem matching_separable_covariance (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x)
    (hmax : ∀ y ∈ G.polytope, separableLower y-maxMatchingEntropy G y ≤
      separableLower x-maxMatchingEntropy G x)
    (u : {e // 0 < x e} → ℝ) :
    u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) ≤
      ∑ e, (1-3*x e.val/(1-x e.val))*((covariance p (matchingNormalized G x) *ᵥ u) e)^2 := by
  let w := matchingScoreWeights x u
  let c := ∑ e, w e*x e
  let a := linearScore G w c
  let v := G.mean (fun M => p M*a M)
  have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p,hp⟩
  have hcenter : ∑ M, p M*a M=0 := by
    dsimp only [a,c]
    rw [linearScore_expectation,hp.2,hp.1.2,mul_one,sub_self]
  have hh := matching_separable_second_variation G hp hopt hmax w c hcenter
  have hzero : ∀ e, ¬0 < x e → v e=0 := by
    intro e he
    have he0 : x e=0 := le_antisymm (le_of_not_gt he) (G.coordinate_mem_Icc hx e).1
    exact mean_score_support G hp.1 a e (by rw [hp.2,he0])
  have hnorm : (∑ e, (v e)^2/x e) =
      ∑ e, ((covariance p (matchingNormalized G x) *ᵥ u) e)^2 := by
    rw [sum_positive_support x _ (fun e he => by rw [hzero e he]; simp)]
    apply Finset.sum_congr rfl
    intro e _
    rw [matchingNormalized_mulVec G hp,div_pow,Real.sq_sqrt e.property.le]
  have hbar : (∑ e, (v e)^2/(1-x e)) =
      ∑ e, x e.val/(1-x e.val)*((covariance p (matchingNormalized G x) *ᵥ u) e)^2 := by
    rw [sum_positive_support x _ (fun e he => by rw [hzero e he]; simp)]
    apply Finset.sum_congr rfl
    intro e _
    rw [matchingNormalized_mulVec G hp,div_pow,Real.sq_sqrt e.property.le]
    change (v e.val)^2/(1-x e.val)=x e.val/(1-x e.val)*((v e.val)^2/x e.val)
    field_simp [ne_of_gt e.property]
  have hquad : (∑ M, p M*(a M)^2)=u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) := by
    rw [covariance_quadratic hp.1.1]
    apply Finset.sum_congr rfl
    intro M _
    rw [← matchingNormalized_score G x u M]
  change -(∑ e, (v e)^2/x e)+3*(∑ e, (v e)^2/(1-x e))+(∑ M,p M*(a M)^2) ≤ 0 at hh
  rw [hnorm,hbar,hquad] at hh
  have heq : (∑ e, (1-3*x e.val/(1-x e.val))*((covariance p (matchingNormalized G x) *ᵥ u) e)^2) =
      (∑ e, ((covariance p (matchingNormalized G x) *ᵥ u) e)^2)-
      3*(∑ e, x e.val/(1-x e.val)*((covariance p (matchingNormalized G x) *ᵥ u) e)^2) := by
    simp_rw [sub_mul,one_mul,Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [heq]
  linarith

omit [Fintype V] [DecidableEq V] in
theorem matching_covariance_diagonal (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) (e : {e // 0<x e}) :
    covariance p (matchingNormalized G x) e e=1-x e.val := by
  rw [covariance_entry hp.1.1]
  have hh := normalizedCentered_variance hp.1.2
    (fun M (e : {e // 0<x e}) => G.indicator M e.val)
    (by intro M e; simp only [LooplessGraph.indicator]; split <;> norm_num)
    (fun e => x e.val) (fun e => congrFun hp.2 e.val) (fun e => e.property) e
  convert hh using 1
  apply Finset.sum_congr rfl
  intro M _
  change p M*matchingNormalized G x M e*matchingNormalized G x M e=
    p M*(matchingNormalized G x M e)^2
  ring

theorem separable_max_has_forced (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hn : 0 < Fintype.card V) (hx : x ∈ G.polytope)
    (hmax : ∀ y ∈ G.polytope, separableLower y-maxMatchingEntropy G y ≤
      separableLower x-maxMatchingEntropy G x) : ∃ e, x e=1 := by
  by_contra hforced
  push Not at hforced
  obtain ⟨p,hp,hopt⟩ := maxMatchingEntropy_attained G hx
  have hsecond := covariance_weighted_rank (covariance_posSemidef p (matchingNormalized G x))
    (fun e => 1-3*x e.val/(1-x e.val)) (matching_separable_covariance G hp hopt hmax)
  have htrace : (∑ e : {e // 0<x e}, (1-3*x e.val/(1-x e.val))*
      covariance p (matchingNormalized G x) e e) = Fintype.card {e // 0<x e}-2*(Fintype.card V:ℝ) := by
    have he (e : {e // 0<x e}) : (1-3*x e.val/(1-x e.val))*
        covariance p (matchingNormalized G x) e e=1-4*x e.val := by
      rw [matching_covariance_diagonal G hp]
      have hh : 1-x e.val ≠ 0 := sub_ne_zero.mpr (Ne.symm (hforced e.val))
      field_simp
      ring
    simp_rw [he]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum]
    obtain ⟨r,hr⟩ := heven
    have hv : Fintype.card V=2*r := by omega
    have hs : (∑ e : {e // 0<x e}, x e.val)=(r:ℝ) := by
      rw [← G.marginal_sum hv hx]
      exact (sum_positive_support x x (fun e he =>
        le_antisymm (le_of_not_gt he) (G.coordinate_mem_Icc hx e).1)).symm
    rw [hs,hv]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Nat.cast_mul,Nat.cast_ofNat]
    ring
  rw [htrace] at hsecond
  have hrank := matching_covariance_rank_face G heven hp hopt
  have hstrict := faceCodimension_strict G heven hn hx
  have hrankR : (Fintype.card {e // 0<x e}:ℝ) ≤ G.faceCodimension x+
      (covariance p (matchingNormalized G x)).rank := by exact_mod_cast hrank
  have hstrictR : (G.faceCodimension x:ℝ)<2*(Fintype.card V:ℝ) := by exact_mod_cast hstrict
  linarith

end MatchingEntropyBounds

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds

namespace LooplessGraph
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def RemainingVertex (G : LooplessGraph V E) (e₀ : E) (v : V) : Prop :=
  ¬G.Incident v e₀

instance remainingVertexDecidable (G : LooplessGraph V E) (e₀ : E) (v : V) :
    Decidable (G.RemainingVertex e₀ v) := inferInstanceAs (Decidable (¬G.Incident v e₀))

def RemainingEdge (G : LooplessGraph V E) (e₀ e : E) : Prop :=
  G.RemainingVertex e₀ (G.left e) ∧ G.RemainingVertex e₀ (G.right e)

instance remainingEdgeDecidable (G : LooplessGraph V E) (e₀ e : E) :
    Decidable (G.RemainingEdge e₀ e) := inferInstanceAs
      (Decidable (G.RemainingVertex e₀ (G.left e) ∧ G.RemainingVertex e₀ (G.right e)))

def deleteEndpoints (G : LooplessGraph V E) (e₀ : E) :
    LooplessGraph {v // G.RemainingVertex e₀ v} {e // G.RemainingEdge e₀ e} where
  left e := ⟨G.left e.val, e.property.1⟩
  right e := ⟨G.right e.val, e.property.2⟩
  loopless e he := G.loopless e.val (congrArg Subtype.val he)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem remainingEdge_ne (G : LooplessGraph V E) (e₀ : E)
    {e : E} (he : G.RemainingEdge e₀ e) : e ≠ e₀ := by
  rintro rfl
  exact he.1 (Or.inl rfl)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem remaining_of_incident (G : LooplessGraph V E) (e₀ : E)
    {e : E} (he : G.RemainingEdge e₀ e) {v : V} (hv : G.Incident v e) :
    G.RemainingVertex e₀ v := by
  rcases hv with h | h
  · exact h ▸ he.1
  · exact h ▸ he.2

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
@[simp] theorem deleteEndpoints_incident (G : LooplessGraph V E) (e₀ : E)
    (v : {v // G.RemainingVertex e₀ v}) (e : {e // G.RemainingEdge e₀ e}) :
    (G.deleteEndpoints e₀).Incident v e ↔ G.Incident v.val e.val := by
  simp only [Incident, deleteEndpoints, Subtype.ext_iff]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem matching_common_vertex (G : LooplessGraph V E) (M : G.Matching)
    {e f : E} (he : e ∈ M.val) (hf : f ∈ M.val) {v : V}
    (hve : G.Incident v e) (hvf : G.Incident v f) : e=f := by
  obtain ⟨g, _, hg⟩ := M.property v
  exact (hg e ⟨he,hve⟩).trans (hg f ⟨hf,hvf⟩).symm

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in

theorem matching_remaining (G : LooplessGraph V E) (e₀ : E) (M : G.Matching)
    (h₀ : e₀ ∈ M.val) {e : E} (he : e ∈ M.val) (hne : e ≠ e₀) :
    G.RemainingEdge e₀ e := by
  constructor
  · intro hv
    exact hne (G.matching_common_vertex M he h₀ (Or.inl rfl) hv)
  · intro hv
    exact hne (G.matching_common_vertex M he h₀ (Or.inr rfl) hv)

def addForced (G : LooplessGraph V E) (e₀ : E) (N : (G.deleteEndpoints e₀).Matching) :
    G.Matching := by
  refine ⟨insert e₀ (N.val.image Subtype.val), ?_⟩
  intro v
  by_cases hv : G.Incident v e₀
  · refine ⟨e₀, ⟨by simp, hv⟩, ?_⟩
    rintro f ⟨hf,hfv⟩
    rcases Finset.mem_insert.mp hf with h | h
    · exact h
    · obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp h
      exact False.elim (G.remaining_of_incident e₀ g.property hfv hv)
  · let v' : {v // G.RemainingVertex e₀ v} := ⟨v,hv⟩
    obtain ⟨f,⟨hf,hfv⟩, hu⟩ := N.property v'
    refine ⟨f.val, ⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨f,hf,rfl⟩),
      (G.deleteEndpoints_incident e₀ v' f).mp hfv⟩, ?_⟩
    rintro g ⟨hg,hgv⟩
    rcases Finset.mem_insert.mp hg with h | h
    · exact False.elim (hv (h ▸ hgv))
    · obtain ⟨g',hg',rfl⟩ := Finset.mem_image.mp h
      exact congrArg Subtype.val (hu g' ⟨hg', (G.deleteEndpoints_incident e₀ v' g').mpr hgv⟩)

omit [Fintype V] [Fintype E] in
@[simp] theorem mem_addForced (G : LooplessGraph V E) (e₀ : E)
    (N : (G.deleteEndpoints e₀).Matching) (e : E) :
    e ∈ (G.addForced e₀ N).val ↔ e=e₀ ∨ ∃ h : G.RemainingEdge e₀ e, ⟨e,h⟩ ∈ N.val := by
  simp only [addForced, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (h | ⟨f,hf,rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨f.property,hf⟩
  · rintro (h | ⟨h,he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨e,h⟩,he,rfl⟩

omit [Fintype V] [Fintype E] in
@[simp] theorem mem_addForced_remaining (G : LooplessGraph V E) (e₀ : E)
    (N : (G.deleteEndpoints e₀).Matching) (e : {e // G.RemainingEdge e₀ e}) :
    e.val ∈ (G.addForced e₀ N).val ↔ e ∈ N.val := by
  rw [mem_addForced]
  simp only [G.remainingEdge_ne e₀ e.property, false_or]
  exact ⟨fun ⟨_,h⟩ => h, fun h => ⟨e.property,h⟩⟩

def removeForced (G : LooplessGraph V E) (e₀ : E)
    (M : {M : G.Matching // e₀ ∈ M.val}) : (G.deleteEndpoints e₀).Matching := by
  refine ⟨M.val.val.subtype (G.RemainingEdge e₀), ?_⟩
  intro v
  obtain ⟨e,⟨he,hev⟩,hu⟩ := M.val.property v.val
  have hne : e ≠ e₀ := by rintro rfl; exact v.property hev
  have hrem := G.matching_remaining e₀ M.val M.property he hne
  refine ⟨⟨e,hrem⟩, ⟨by simpa using he,
    (G.deleteEndpoints_incident e₀ v ⟨e,hrem⟩).mpr hev⟩, ?_⟩
  rintro f ⟨hf,hfv⟩
  apply Subtype.ext
  exact hu f.val ⟨by simpa using hf, (G.deleteEndpoints_incident e₀ v f).mp hfv⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
@[simp] theorem mem_removeForced (G : LooplessGraph V E) (e₀ : E)
    (M : {M : G.Matching // e₀ ∈ M.val}) (e : {e // G.RemainingEdge e₀ e}) :
    e ∈ (G.removeForced e₀ M).val ↔ e.val ∈ M.val.val := by
  simp [removeForced]

def forcedMatchingEquiv (G : LooplessGraph V E) (e₀ : E) :
    (G.deleteEndpoints e₀).Matching ≃ {M : G.Matching // e₀ ∈ M.val} where
  toFun N := ⟨G.addForced e₀ N, (G.mem_addForced e₀ N e₀).mpr (Or.inl rfl)⟩
  invFun M := G.removeForced e₀ M
  left_inv N := by
    apply Subtype.ext
    ext e
    exact (G.mem_removeForced e₀ _ e).trans (G.mem_addForced_remaining e₀ N e)
  right_inv M := by
    apply Subtype.ext
    apply Subtype.ext
    ext e
    rw [mem_addForced]
    constructor
    · rintro (rfl | ⟨h,he⟩)
      · exact M.property
      · exact (G.mem_removeForced e₀ M ⟨e,h⟩).mp he
    · intro he
      by_cases h : e=e₀
      · exact Or.inl h
      · exact Or.inr ⟨G.matching_remaining e₀ M.val M.property he h,
          (G.mem_removeForced e₀ M _).mpr he⟩

omit [Fintype V] [Fintype E] in
theorem addForced_injective (G : LooplessGraph V E) (e₀ : E) :
    Function.Injective (G.addForced e₀) := by
  intro N N' h
  apply (G.forcedMatchingEquiv e₀).injective
  exact Subtype.ext h

omit [Fintype E] [DecidableEq E] in
theorem remaining_vertex_card (G : LooplessGraph V E) (e₀ : E) :
    Fintype.card {v // G.RemainingVertex e₀ v} + 2 = Fintype.card V := by
  have he : Fintype.card {v // G.Incident v e₀}=2 := by
    rw [Fintype.card_subtype]
    have hf : Finset.univ.filter (fun v => G.Incident v e₀)={G.left e₀, G.right e₀} := by
      ext v
      simp [Incident, eq_comm]
    rw [hf, Finset.card_pair (G.loopless e₀)]
  have h := Fintype.card_subtype_compl (G.Incident · e₀)
  have hle := Fintype.card_subtype_le (G.Incident · e₀)
  change Fintype.card {v // ¬G.Incident v e₀} + 2 = Fintype.card V
  omega

omit [Fintype V] [Fintype E] in
@[simp] theorem range_addForced (G : LooplessGraph V E) (e₀ : E) (M : G.Matching) :
    M ∈ Set.range (G.addForced e₀) ↔ e₀ ∈ M.val := by
  constructor
  · rintro ⟨N,rfl⟩
    exact (G.mem_addForced e₀ N e₀).mpr (Or.inl rfl)
  · intro h
    refine ⟨G.removeForced e₀ ⟨M,h⟩, ?_⟩
    exact congrArg Subtype.val ((G.forcedMatchingEquiv e₀).apply_symm_apply ⟨M,h⟩)

omit [Fintype V] [DecidableEq V] in
theorem law_support_of_mean_one (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) {e₀ : E} (he : G.mean p e₀=1)
    (M : G.Matching) (hM : e₀ ∉ M.val) : p M=0 := by
  have hz : ∑ N, p N*(1-G.indicator N e₀)=0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hp.2]
    change 1-G.mean p e₀=0
    rw [he, sub_self]
  have hh := (Finset.sum_eq_zero_iff_of_nonneg
    (fun N (_ : N ∈ Finset.univ) =>
      mul_nonneg (hp.1 N) (sub_nonneg.mpr (G.indicator_le_one N e₀)))).mp hz M (by simp)
  simpa [indicator,hM] using hh

omit [Fintype V] in

theorem forcedLaw_feasible (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) (e₀ : E) (he : x e₀=1) :
    (fun N => p (G.addForced e₀ N)) ∈ (G.deleteEndpoints e₀).feasibleLaws
      (fun e => x e.val) := by
  have hs : ∀ M, e₀ ∉ M.val → p M=0 :=
    G.law_support_of_mean_one hp.1 (by rw [hp.2,he])
  refine ⟨⟨fun N => hp.1.1 _, ?_⟩, ?_⟩
  · rw [← hp.1.2]
    apply Fintype.sum_of_injective (G.addForced e₀) (G.addForced_injective e₀)
    · intro M hM
      exact hs M (fun hh => hM ((G.range_addForced e₀ M).mpr hh))
    · intro N
      rfl
  · funext e
    rw [← congrFun hp.2 e.val]
    apply Fintype.sum_of_injective (G.addForced e₀) (G.addForced_injective e₀)
    · intro M hM
      rw [hs M (fun hh => hM ((G.range_addForced e₀ M).mpr hh)),zero_mul]
    · intro N
      simp only [indicator,mem_addForced_remaining]

omit [Fintype V] [DecidableEq V] in

theorem forced_coordinate_zero (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (e₀ : E) (he : x e₀=1) {e : E}
    (hneq : e ≠ e₀) (hrem : ¬G.RemainingEdge e₀ e) : x e=0 := by
  obtain ⟨p,hp⟩ := (G.mem_polytope_iff x).mp hx
  rw [← congrFun hp.2 e]
  apply Finset.sum_eq_zero
  intro M _
  by_cases hM : e₀ ∈ M.val
  · have hh : e ∉ M.val := fun hh => hrem (G.matching_remaining e₀ M hM hh hneq)
    simp [indicator,hh]
  · rw [G.law_support_of_mean_one hp.1 (by rw [hp.2,he]) M hM,zero_mul]

omit [Fintype V] in

theorem separableLower_forced (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (e₀ : E) (he : x e₀=1) :
    separableLower (fun e : {e // G.RemainingEdge e₀ e} => x e.val)=separableLower x := by
  have hz : ∀ e, ¬G.RemainingEdge e₀ e →
      Real.negMulLog (x e)=0 ∧ Real.negMulLog (1-x e)=0 := by
    intro e h
    by_cases hneq : e=e₀
    · simp [hneq,he]
    · simp [G.forced_coordinate_zero hx e₀ he hneq h]
  unfold separableLower entropy
  rw [sum_subtype_supported _ _ (fun e h => (hz e h).1),
    sum_subtype_supported _ _ (fun e h => (hz e h).2)]

end LooplessGraph

theorem entropy_fiberMass_injective {A : Type uA} {B : Type uB} [Fintype A] [Fintype B] [DecidableEq B]
    (p : A → ℝ) (f : A → B) (hf : Function.Injective f) :
    entropy (fiberMass p f)=entropy p := by
  classical
  have hself (a : A) : fiberMass p f (f a)=p a := by
    simp [fiberMass,hf.eq_iff]
  have hzero (b : B) (hb : b ∉ Set.range f) : fiberMass p f b=0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact ite_eq_right (fun h => hb ⟨a,h⟩)
  symm
  apply Fintype.sum_of_injective f hf
  · intro b hb
    rw [hzero b hb,Real.negMulLog_zero]
  · intro a
    rw [hself]

namespace LooplessGraph
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
omit [Fintype V] in

theorem liftForced_feasible (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (e₀ : E) (he : x e₀=1)
    {q : (G.deleteEndpoints e₀).Matching → ℝ}
    (hq : q ∈ (G.deleteEndpoints e₀).feasibleLaws (fun e => x e.val)) :
    fiberMass q (G.addForced e₀) ∈ G.feasibleLaws x := by
  refine ⟨fiberMass_mem_simplex hq.1 _, ?_⟩
  funext e
  rw [mean,fiberMass_expect]
  by_cases heq : e=e₀
  · subst e
    simpa [indicator] using hq.1.2.trans he.symm
  · by_cases hr : G.RemainingEdge e₀ e
    · change (∑ N, q N*G.indicator (G.addForced e₀ N) e)=_
      have hm (N : (G.deleteEndpoints e₀).Matching) :
          G.indicator (G.addForced e₀ N) e = (G.deleteEndpoints e₀).indicator N ⟨e,hr⟩ := by
        simp only [indicator,G.mem_addForced_remaining e₀ N ⟨e,hr⟩]
      simp_rw [hm]
      exact congrFun hq.2 ⟨e,hr⟩
    · rw [G.forced_coordinate_zero hx e₀ he heq hr]
      apply Finset.sum_eq_zero
      intro N _
      simp [indicator,heq,hr]

omit [Fintype V] in

theorem maxMatchingEntropy_forced_le (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (e₀ : E) (he : x e₀=1) :
    maxMatchingEntropy (G.deleteEndpoints e₀) (fun e => x e.val) ≤ maxMatchingEntropy G x := by
  obtain ⟨p,hp⟩ := (G.mem_polytope_iff x).mp hx
  have hr := G.forcedLaw_feasible hp e₀ he
  have hx' := ((G.deleteEndpoints e₀).mem_polytope_iff _).mpr ⟨_,hr⟩
  obtain ⟨q,hq,hopt⟩ := maxMatchingEntropy_attained (G.deleteEndpoints e₀) hx'
  rw [← hopt,← entropy_fiberMass_injective q _ (G.addForced_injective e₀)]
  exact entropy_le_maxMatchingEntropy G (G.liftForced_feasible hx e₀ he hq)

end LooplessGraph

end MatchingEntropyBounds

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds

theorem separable_lower_aux (n : ℕ) :
    ∀ {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessGraph V E), Fintype.card V=n → Even n →
      ∀ x ∈ G.polytope, separableLower x ≤ maxMatchingEntropy G x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V E _ _ _ _ G hcard heven y hy
    by_cases hn : n=0
    · have : IsEmpty V := Fintype.card_eq_zero_iff.mp (hcard.trans hn)
      have : IsEmpty E := ⟨fun e => isEmptyElim (G.left e)⟩
      simpa [separableLower,entropy] using maxMatchingEntropy_nonneg G hy
    · have heven' : Even (Fintype.card V) := hcard ▸ heven
      have hPM : Nonempty G.Matching := by
        obtain ⟨p,hp⟩ := (G.mem_polytope_iff y).mp hy
        by_contra h
        have : IsEmpty G.Matching := not_nonempty_iff.mp h
        simpa using hp.1.2
      obtain ⟨x,hx,hmax⟩ := separableDefect_attains_max G heven' hPM
      obtain ⟨e₀,he₀⟩ := separable_max_has_forced G heven' (by omega) hx hmax
      have hc := G.remaining_vertex_card e₀
      have hlt : Fintype.card {v // G.RemainingVertex e₀ v}<n := by omega
      have hev : Even (Fintype.card {v // G.RemainingVertex e₀ v}) := by
        obtain ⟨r,hr⟩ := heven
        refine ⟨r-1,?_⟩
        omega
      obtain ⟨p,hp⟩ := (G.mem_polytope_iff x).mp hx
      have hs := G.forcedLaw_feasible hp e₀ he₀
      have hxr := ((G.deleteEndpoints e₀).mem_polytope_iff _).mpr ⟨_,hs⟩
      have hsmall := ih _ hlt (G.deleteEndpoints e₀) rfl hev _ hxr
      rw [G.separableLower_forced hx e₀ he₀] at hsmall
      have hxbound := hsmall.trans (G.maxMatchingEntropy_forced_le hx e₀ he₀)
      have hcompare := hmax y hy
      linarith

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem separable_lower (G : LooplessGraph V E) (hPM : Nonempty G.Matching)
    (x : E → ℝ) (hx : x ∈ G.polytope) : separableLower x ≤ maxMatchingEntropy G x := by
  obtain ⟨M⟩ := hPM
  have hev : Even (Fintype.card V) := ⟨M.val.card, by have hh := G.matching_card_twice M; omega⟩
  exact separable_lower_aux (Fintype.card V) G rfl hev x hx

end MatchingEntropyBounds

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds

theorem entropy_le_subprob_crossEntropy {I : Type uI} [Fintype I] {p q : I → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i ≤ 1) (hq : q ∈ probabilitySimplex I)
    (hsupp : ∀ i, p i=0 → q i=0) :
    entropy q ≤ -∑ i, q i*Real.log (p i) := by
  have hterm : ∀ i, Real.negMulLog (q i) ≤ -(q i*Real.log (p i))+p i-q i := by
    intro i
    by_cases hi : p i=0
    · simp [hi,hsupp i hi]
    · simpa only [neg_mul] using negMulLog_tangent (hq.1 i)
        (lt_of_le_of_ne (hp i) (Ne.symm hi))
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ => hterm i
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_neg_distrib,hq.2] at hh
  change entropy q ≤ -(∑ i, q i*Real.log (p i))+(∑ i,p i)-1 at hh
  linarith

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

def matchingBits (G : LooplessGraph V E) (M : G.Matching) : E → Bool :=
  fun e => decide (e ∈ M.val)

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem matchingBits_injective (G : LooplessGraph V E) : Function.Injective G.matchingBits := by
  intro M N h
  apply Subtype.ext
  ext e
  have he := congrFun h e
  simpa only [matchingBits,decide_eq_decide] using he

end LooplessGraph

def productBoolean (x : E → ℝ) (b : E → Bool) : ℝ :=
  ∏ e, if b e then x e else 1-x e

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem productBoolean_nonneg {x : E → ℝ} (hx : ∀ e, x e ∈ Set.Icc (0:ℝ) 1)
    (b : E → Bool) : 0 ≤ productBoolean x b := by
  apply Finset.prod_nonneg
  intro e _
  split
  · exact (hx e).1
  · exact sub_nonneg.mpr (hx e).2

omit [Fintype V] [DecidableEq V] in
theorem productBoolean_sum (x : E → ℝ) : (∑ b : E → Bool, productBoolean x b)=1 := by
  unfold productBoolean
  rw [← Fintype.prod_sum (fun e (b : Bool) => if b then x e else 1-x e)]
  simp

omit [Fintype V] [DecidableEq V] in
theorem matchingBoolean_sum_le (G : LooplessGraph V E) {x : E → ℝ}
    (hx : ∀ e, x e ∈ Set.Icc (0:ℝ) 1) :
    (∑ M, productBoolean x (G.matchingBits M)) ≤ 1 := by
  rw [← productBoolean_sum x]
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image G.matchingBits, productBoolean x b := by
      rw [Finset.sum_image]
      intro M _ N _ h
      exact G.matchingBits_injective h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun b _ _ => productBoolean_nonneg hx b)

omit [Fintype V] [DecidableEq V] in
theorem matching_boolean_factor_pos (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) {M : G.Matching} (hM : 0<p M) (e : E) :
    0<(if G.matchingBits M e then x e else 1-x e) := by
  unfold LooplessGraph.matchingBits
  by_cases he : e ∈ M.val
  · simp only [he,decide_true,ite_true]
    have hh := Finset.single_le_sum (f := fun N => p N*G.indicator N e)
      (s := Finset.univ) (fun N _ => mul_nonneg (hp.1.1 N) (G.indicator_nonneg N e))
      (Finset.mem_univ M)
    have hm : G.indicator M e=1 := by simp [LooplessGraph.indicator,he]
    rw [hm,mul_one] at hh
    change p M ≤ G.mean p e at hh
    rw [hp.2] at hh
    exact hM.trans_le hh
  · simp only [he,decide_false]
    have hh := Finset.single_le_sum (f := fun N => p N*(1-G.indicator N e))
      (s := Finset.univ) (fun N _ => mul_nonneg (hp.1.1 N)
        (sub_nonneg.mpr (G.indicator_le_one N e))) (Finset.mem_univ M)
    have hm : G.indicator M e=0 := by simp [LooplessGraph.indicator,he]
    simp only [hm,sub_zero,mul_one,mul_sub,Finset.sum_sub_distrib,hp.1.2] at hh
    change p M ≤ 1-G.mean p e at hh
    rw [hp.2] at hh
    exact hM.trans_le hh

omit [Fintype V] [DecidableEq V] in

theorem matching_entropy_le_binary (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) : entropy p ≤ binaryEntropy x := by
  have hx := G.coordinate_mem_Icc ((G.mem_polytope_iff x).mpr ⟨p,hp⟩)
  have hprod (M : G.Matching) (hM : 0<p M) : 0<productBoolean x (G.matchingBits M) :=
    Finset.prod_pos (fun e _ => matching_boolean_factor_pos G hp hM e)
  have hcross := entropy_le_subprob_crossEntropy
    (fun M => productBoolean_nonneg hx (G.matchingBits M)) (matchingBoolean_sum_le G hx) hp.1
    (fun M hzero => le_antisymm (le_of_not_gt (fun hM => (ne_of_gt (hprod M hM)) hzero)) (hp.1.1 M))
  have hlog (M : G.Matching) : p M*Real.log (productBoolean x (G.matchingBits M)) =
      ∑ e, p M*(G.indicator M e*Real.log (x e)+(1-G.indicator M e)*Real.log (1-x e)) := by
    by_cases hzero : p M=0
    · simp [hzero]
    · have hpos : 0<p M := lt_of_le_of_ne (hp.1.1 M) (Ne.symm hzero)
      rw [productBoolean,Real.log_prod (fun e _ => ne_of_gt (matching_boolean_factor_pos G hp hpos e)),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      simp only [LooplessGraph.matchingBits,LooplessGraph.indicator]
      by_cases he : e ∈ M.val <;> simp [he]
  have heq : -(∑ M, p M*Real.log (productBoolean x (G.matchingBits M)))=binaryEntropy x := by
    simp_rw [hlog]
    rw [Finset.sum_comm]
    have he (e : E) : (∑ M, p M*(G.indicator M e*Real.log (x e)+
        (1-G.indicator M e)*Real.log (1-x e)))=
        x e*Real.log (x e)+(1-x e)*Real.log (1-x e) := by
      simp_rw [mul_add,← mul_assoc,Finset.sum_add_distrib,← Finset.sum_mul]
      have hmean : (∑ M,p M*G.indicator M e)=x e := congrFun hp.2 e
      have hbar : (∑ M,p M*(1-G.indicator M e))=1-x e := by
        simp_rw [mul_sub,mul_one,Finset.sum_sub_distrib,hp.1.2,hmean]
      rw [hmean,hbar]
    simp_rw [he]
    rw [Finset.sum_add_distrib,neg_add_rev]
    dsimp only [binaryEntropy]
    rw [entropy_eq,entropy_eq]
    ring
  rwa [heq] at hcross

omit [Fintype V] [DecidableEq V] in
theorem maxMatchingEntropy_le_binary (G : LooplessGraph V E) (x : E → ℝ)
    (hx : x ∈ G.polytope) : maxMatchingEntropy G x ≤ binaryEntropy x := by
  obtain ⟨p,hp,hopt⟩ := maxMatchingEntropy_attained G hx
  rw [← hopt]
  exact matching_entropy_le_binary G hp

end MatchingEntropyBounds

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem separable_entropy_main (G : LooplessGraph V E)
    (_hn : 2 ≤ Fintype.card V) (hPM : Nonempty G.Matching)
    (x : E → ℝ) (hx : x ∈ G.polytope) :
    separableLower x ≤ maxMatchingEntropy G x ∧
      maxMatchingEntropy G x ≤ binaryEntropy x :=
  ⟨separable_lower G hPM x hx, maxMatchingEntropy_le_binary G x hx⟩

omit [Fintype V] [Fintype E] [DecidableEq V] in

theorem selected_uniform_mean (G : LooplessGraph V E) {k : ℕ} (hk : 1 ≤ k)
    (M : Fin k → G.Matching)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (M i).val (M j).val) :
    ∃ x ∈ G.polytope, ∀ e, x e=0 ∨ x e=1/(k:ℝ) := by
  classical
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hsum : (∑ i : Fin k, (1/(k:ℝ)))=1 := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  let x := ∑ i : Fin k, (1/(k:ℝ)) • G.indicator (M i)
  refine ⟨x,?_,?_⟩
  · exact (convex_convexHull ℝ (Set.range G.indicator)).sum_mem
      (fun (i : Fin k) _ => (one_div_pos.mpr hkR).le) hsum
      (fun i _ => subset_convexHull ℝ _ (Set.mem_range_self (M i)))
  · intro e
    dsimp only [x]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    by_cases he : ∃ i, e ∈ (M i).val
    · obtain ⟨i,hi⟩ := he
      right
      rw [Finset.sum_eq_single i]
      · simp [LooplessGraph.indicator,hi]
      · intro j _ hji
        have hj : e ∉ (M j).val := fun h =>
          Finset.disjoint_left.mp (hdisjoint j i hji) h hi
        simp [LooplessGraph.indicator,hj]
      · simp
    · left
      apply Finset.sum_eq_zero
      intro i _
      have hi : e ∉ (M i).val := fun h => he ⟨i,h⟩
      simp [LooplessGraph.indicator,hi]

theorem separableLower_uniform (G : LooplessGraph V E) {r k : ℕ}
    (hV : Fintype.card V=2*r) (hk : 2 ≤ k) {x : E → ℝ} (hx : x ∈ G.polytope)
    (huniform : ∀ e, x e=0 ∨ x e=1/(k:ℝ)) :
    separableLower x = (r:ℝ)*(Real.log (k:ℝ)+
      (3*((k-1:ℕ):ℝ))*Real.log (1-1/(k:ℝ))) := by
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hkcast : ((k-1:ℕ):ℝ)=(k:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have ha (e : E) : Real.negMulLog (x e)=x e*Real.log (k:ℝ) := by
    rcases huniform e with he | he
    · simp [he]
    · rw [he,one_div,Real.negMulLog,Real.log_inv]
      ring
  have hb (e : E) : Real.negMulLog (1-x e)=
      -((k:ℝ)-1)*x e*Real.log (1-1/(k:ℝ)) := by
    rcases huniform e with he | he
    · simp [he]
    · rw [he,Real.negMulLog]
      field_simp
  unfold separableLower entropy
  simp_rw [ha,hb]
  rw [← Finset.sum_mul,← Finset.sum_mul,← Finset.mul_sum,G.marginal_sum hV hx,hkcast]
  ring

theorem structuralBase_eq_exp {k : ℕ} (hk : 2 ≤ k) :
    structuralBase k = Real.exp (Real.log (k:ℝ)+
      (3*((k-1:ℕ):ℝ))*Real.log (1-1/(k:ℝ))) := by
  have hkR : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have ht : 0<1-1/(k:ℝ) := by
    have hh := (div_lt_one (by linarith : (0:ℝ)<k)).mpr hkR
    linarith
  rw [structuralBase,ite_eq_right (by omega),Real.exp_add,Real.exp_log (by linarith)]
  have hc : (3*((k-1:ℕ):ℝ)) = ((3*(k-1):ℕ):ℝ) := by push_cast; ring
  rw [hc,Real.exp_nat_mul,Real.exp_log ht]

theorem structuralBase_lower {k : ℕ} (hk : 1 ≤ k) :
    Real.exp (-3)*(k:ℝ) ≤ structuralBase k := by
  by_cases hk1 : k=1
  · subst k
    simp only [structuralBase,ite_true,Nat.cast_one,mul_one]
    exact Real.exp_le_one_iff.mpr (by norm_num)
  · have hk2 : 2 ≤ k := by omega
    have hkR : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
    have hk0 : (0:ℝ)<k := by linarith
    have ht : 0<1-1/(k:ℝ) := sub_pos.mpr ((div_lt_one hk0).mpr hkR)
    have hb := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
    rw [Real.log_inv] at hb
    have hkm : 0<(k:ℝ)-1 := by linarith
    have heq : ((1-1/(k:ℝ))⁻¹-1)*((k:ℝ)-1)=1 := by
      field_simp
      ring
    have hh := mul_le_mul_of_nonneg_right hb hkm.le
    rw [heq] at hh
    have hlog : -1 ≤ ((k:ℝ)-1)*Real.log (1-1/(k:ℝ)) := by nlinarith
    rw [structuralBase_eq_exp hk2]
    have hkcast : ((k-1:ℕ):ℝ)=(k:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
    have hbase : Real.exp (-3)*(k:ℝ)=Real.exp (-3+Real.log (k:ℝ)) := by
      rw [Real.exp_add,Real.exp_log hk0]
    rw [hbase]
    apply Real.exp_le_exp.mpr
    rw [hkcast]
    nlinarith

theorem uniform_support_count (G : LooplessGraph V E) {r k : ℕ}
    (hV : Fintype.card V=2*r) (hk : 1 ≤ k) {x : E → ℝ} (hx : x ∈ G.polytope)
    (huniform : ∀ e, x e=0 ∨ x e=1/(k:ℝ)) :
    structuralBase k ^ r ≤ (Fintype.card G.Matching : ℝ) ∧
      (Real.exp (-3)*(k:ℝ)) ^ r ≤ structuralBase k ^ r := by
  have hPM : Nonempty G.Matching := by
    obtain ⟨p,hp⟩ := (G.mem_polytope_iff x).mp hx
    by_contra h
    have : IsEmpty G.Matching := not_nonempty_iff.mp h
    simpa using hp.1.2
  have hN : (0:ℝ)<Fintype.card G.Matching := by
    exact_mod_cast Fintype.card_pos_iff.mpr hPM
  constructor
  · by_cases hk1 : k=1
    · subst k
      simp only [structuralBase,ite_true,one_pow]
      exact_mod_cast (Fintype.card_pos_iff.mpr hPM)
    · have hk2 : 2 ≤ k := by omega
      have hlog := (separable_lower G hPM x hx).trans (maxMatchingEntropy_le_log_card G hx)
      rw [separableLower_uniform G hV hk2 hx huniform] at hlog
      have he := Real.exp_le_exp.mpr hlog
      rw [Real.exp_log hN,Real.exp_nat_mul,← structuralBase_eq_exp hk2] at he
      exact he
  · exact pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _))
      (structuralBase_lower hk) r

theorem structural_count_main (G : LooplessGraph V E) (r k : ℕ)
    (_hr : 0<r) (hV : Fintype.card V=2*r) (hk : 1 ≤ k)
    (M : Fin k → G.Matching)
    (hdisjoint : ∀ i j, i≠j → Disjoint (M i).val (M j).val) :
    structuralBase k ^ r ≤ (Fintype.card G.Matching : ℝ) ∧
      (Real.exp (-3)*(k:ℝ)) ^ r ≤ structuralBase k ^ r := by
  obtain ⟨x,hx,hu⟩ := selected_uniform_mean G hk M hdisjoint
  exact uniform_support_count G hV hk hx hu

theorem regular_uniform_mem (G : LooplessGraph V E) {r k : ℕ}
    (hV : Fintype.card V=2*r) (hk : 1 ≤ k)
    (hregular : ∀ v, (Finset.univ.filter (G.Incident v)).card=k)
    (hodd : ∀ S : Finset V, Odd S.card → k ≤ (G.cut S).card) :
    (fun _ : E => 1/(k:ℝ)) ∈ G.polytope := by
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  rw [G.polytope_eq_constraints (by rw [hV]; exact even_two_mul r)]
  refine ⟨fun _ => (one_div_pos.mpr hkR).le,?_,?_⟩
  · intro v
    unfold LooplessGraph.degree
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul,hregular]
    field_simp
  · intro S hS
    unfold LooplessGraph.cutMass
    simp only [Finset.sum_const,nsmul_eq_mul]
    have hc : (k:ℝ) ≤ (G.cut S).card := by exact_mod_cast hodd S hS
    calc
      1 = (k:ℝ)*(1/(k:ℝ)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (one_div_pos.mpr hkR).le

theorem regular_count_main (G : LooplessGraph V E) (r k : ℕ)
    (_hr : 0<r) (hV : Fintype.card V=2*r) (hk : 1 ≤ k)
    (hregular : ∀ v, (Finset.univ.filter (G.Incident v)).card=k)
    (hodd : ∀ S : Finset V, Odd S.card → k ≤ (G.cut S).card) :
    structuralBase k ^ r ≤ (Fintype.card G.Matching : ℝ) ∧
      (Real.exp (-3)*(k:ℝ)) ^ r ≤ structuralBase k ^ r := by
  exact uniform_support_count G hV hk (regular_uniform_mem G hV hk hregular hodd)
    (fun _ => Or.inr rfl)

end MatchingEntropyBounds

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter Module


namespace MatchingEntropyBounds.Refined

section SharedEquation
variable {A : Type uA} {B : Type uB} {C : Type uC} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module ℝ A] [Module ℝ B] [Module ℝ C]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]

theorem quotient_finrank_shared (U : Submodule ℝ A) (W : Submodule ℝ B) (Z : Submodule ℝ C)
    (f : A →ₗ[ℝ] B) (g : A →ₗ[ℝ] C)
    (h : ∀ u, f u ∈ W → g u ∈ Z → u ∈ U)
    (l : B →ₗ[ℝ] ℝ) (r : C →ₗ[ℝ] ℝ) (hl : W ≤ l.ker) (hr : Z ≤ r.ker)
    (heq : ∀ u, l (f u) = r (g u)) (b : B) (hb : l b ≠ 0) :
    finrank ℝ (A ⧸ U) + 1 ≤ finrank ℝ (B ⧸ W) + finrank ℝ (C ⧸ Z) := by
  let F := (W.mkQ.comp f).prod (Z.mkQ.comp g)
  let L : ((B ⧸ W) × (C ⧸ Z)) →ₗ[ℝ] ℝ :=
    (W.liftQ l hl).comp (LinearMap.fst ℝ _ _) -
      (Z.liftQ r hr).comp (LinearMap.snd ℝ _ _)
  have hk : F.ker ≤ U := by
    intro u hu
    have hh : (W.mkQ (f u), Z.mkQ (g u)) = 0 := hu
    apply h u
    · simpa using congrArg Prod.fst hh
    · simpa using congrArg Prod.snd hh
  have hL : ∀ u, F u ∈ L.ker := by
    intro u
    change l (f u) - r (g u) = 0
    exact sub_eq_zero.mpr (heq u)
  let F' := F.codRestrict L.ker hL
  have hk' : F'.ker ≤ U := by
    intro u hu
    apply hk
    have hh := congrArg Subtype.val (show F' u = 0 from hu)
    exact hh
  have hdim := quotient_finrank_le_of_ker_le U F' hk'
  have hsum := L.finrank_range_add_finrank_ker
  have hpos : 1 ≤ finrank ℝ L.range := by
    apply Submodule.one_le_finrank_iff.mpr
    intro hh
    have hm : L (W.mkQ b, 0) ∈ L.range := ⟨_, rfl⟩
    rw [hh] at hm
    have hz : L (W.mkQ b, 0) = 0 := hm
    apply hb
    simpa [L] using hz
  rw [Module.finrank_prod] at hsum
  omega
end SharedEquation

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def lowerObjective (c : ℝ) (x : E → ℝ) : ℝ := entropy x - c * complementEntropy x

open LooplessGraph

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem positiveExtension_self {x : E → ℝ} (hx : ∀ e, 0 ≤ x e) :
    positiveExtension x (fun e => x e.val) = x := by
  funext e
  by_cases he : 0 < x e
  · simp [positiveExtension, he]
  · simp [positiveExtension, le_antisymm (le_of_not_gt he) (hx e)]

def boundaryLinear (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) :
    ({e // 0 < G.sideMarginal x S e} → ℝ) →ₗ[ℝ] ℝ :=
  (LinearMap.proj none).comp
    ((G.onSide S).degreeLinear.comp (positiveExtension (G.sideMarginal x S)))

omit [Fintype V] [DecidableEq E] in
theorem boundaryLinear_restriction (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V)
    (u : {e // 0 < x e} → ℝ) :
    boundaryLinear G x S (G.sideRestriction x S u) = G.cutMass (positiveExtension x u) S := by
  change (G.onSide S).degree (fun e => positiveExtension x u e.val) none = _
  exact G.onSide_degree_none S _

omit [Fintype V] [DecidableEq E] in
theorem boundaryLinear_face (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) :
    (G.onSide S).faceSpace (G.sideMarginal x S) ≤ (boundaryLinear G x S).ker := by
  intro u hu
  exact congrFun hu.1 none

theorem faceCodimension_le_sides_shared (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.constraintPolytope)
    (S : Finset V) (hS : Odd S.card) (ht : G.cutMass x S = 1) :
    G.faceCodimension x + 1 ≤ (G.onSide S).faceCodimension (G.sideMarginal x S) +
      (G.onSide Sᶜ).faceCodimension (G.sideMarginal x Sᶜ) := by
  classical
  apply quotient_finrank_shared (G.faceSpace x)
    ((G.onSide S).faceSpace (G.sideMarginal x S))
    ((G.onSide Sᶜ).faceSpace (G.sideMarginal x Sᶜ))
    (G.sideRestriction x S) (G.sideRestriction x Sᶜ)
    (fun _ => G.faceSpace_of_side_spaces heven hx S hS ht)
    (boundaryLinear G x S) (boundaryLinear G x Sᶜ)
    (boundaryLinear_face G x S) (boundaryLinear_face G x Sᶜ)
    (fun u => by simp only [boundaryLinear_restriction, cutMass, cut_compl])
    (fun e => G.sideMarginal x S e.val)
  have hext := positiveExtension_self (x := G.sideMarginal x S) (fun e => hx.1 e.val)
  change (G.onSide S).degree
    (positiveExtension (G.sideMarginal x S) (fun e => G.sideMarginal x S e.val)) none ≠ 0
  rw [hext, G.onSide_degree_none, ht]
  norm_num

omit [Fintype E] [DecidableEq E] in

theorem incident_of_card_two (G : LooplessGraph V E) (hV : Fintype.card V = 2)
    (v : V) (e : E) : G.Incident v e := by
  have hp : ({G.left e, G.right e} : Finset V) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hV, G.loopless e]
  have hv : v ∈ ({G.left e, G.right e} : Finset V) := hp ▸ Finset.mem_univ v
  simpa only [Finset.mem_insert, Finset.mem_singleton, eq_comm, Incident] using hv

omit [DecidableEq E] in

theorem faceCodimension_two (G : LooplessGraph V E) (hV : Fintype.card V = 2)
    (x : E → ℝ) : G.faceCodimension x ≤ 1 := by
  classical
  let L : ({e // 0 < x e} → ℝ) →ₗ[ℝ] ℝ :=
    (Finset.univ.sum (fun e : E => LinearMap.proj e)).comp (positiveExtension x)
  have heven : Even (Fintype.card V) := by simp [hV]
  have hnt : ¬ ∃ S : Finset V, Odd S.card ∧ 3 ≤ S.card ∧ 3 ≤ Sᶜ.card ∧ G.cutMass x S = 1 := by
    rintro ⟨S, _, hlo, _, _⟩
    have hc := Finset.card_le_univ S
    omega
  have hker : L.ker ≤ G.faceSpace x := by
    intro u hu
    have hz : ∑ e, positiveExtension x u e = 0 := by simpa [L] using hu
    have hd : ∀ v, G.degree (positiveExtension x u) v = 0 := by
      intro v
      simpa only [degree, incident_of_card_two G hV v, ite_true] using hz
    refine ⟨funext hd, ?_⟩
    exact G.trivial_tight_cut_preserved heven hnt _ hd
  simpa [faceCodimension] using quotient_finrank_le_of_ker_le (G.faceSpace x) L hker

theorem sharp_face_rank_aux (n : ℕ) :
    ∀ {W : Type uW} {F : Type uF} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
      (G : LooplessGraph W F), Fintype.card W=n → Even n → 4≤n →
      ∀ x ∈ G.constraintPolytope, 2 * (G.faceCodimension x + 2) ≤ 3 * n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W F _ _ _ _ G hcard heven hfour x hx
    have heven' : Even (Fintype.card W) := hcard ▸ heven
    by_cases hcut : ∃ S : Finset W, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1
    · obtain ⟨S,hS,hlo,hhi,ht⟩ := hcut
      have hc := odd_compl_of_even heven' hS
      have hlt1 : Fintype.card (Option {v // v ∈ S}) < n := by
        simp only [Fintype.card_option,Fintype.card_coe]
        have hco := Finset.card_compl S
        omega
      have hlt2 : Fintype.card (Option {v // v ∈ Sᶜ}) < n := by
        simp only [Fintype.card_option,Fintype.card_coe]
        have hco := Finset.card_compl S
        have hle := Finset.card_le_univ S
        omega
      have hv1 : Even (Fintype.card (Option {v // v ∈ S})) := by
        simpa only [Fintype.card_option,Fintype.card_coe] using hS.add_odd odd_one
      have hv2 : Even (Fintype.card (Option {v // v ∈ Sᶜ})) := by
        simpa only [Fintype.card_option,Fintype.card_coe] using hc.add_odd odd_one
      have hn1 : 4≤Fintype.card (Option {v // v ∈ S}) := by
        simp only [Fintype.card_option,Fintype.card_coe]; omega
      have hn2 : 4≤Fintype.card (Option {v // v ∈ Sᶜ}) := by
        simp only [Fintype.card_option,Fintype.card_coe]; omega
      have hx1 := G.restriction_mem_constraints hx S hS ht
      have htc : G.cutMass x Sᶜ=1 := by simpa only [cutMass,cut_compl] using ht
      have hx2 := G.restriction_mem_constraints hx Sᶜ hc htc
      have hb1 := ih _ hlt1 (G.onSide S) rfl hv1 hn1 _ hx1
      have hb2 := ih _ hlt2 (G.onSide Sᶜ) rfl hv2 hn2 _ hx2
      have hb := faceCodimension_le_sides_shared G heven' hx S hS ht
      have hsum : Fintype.card (Option {v // v ∈ S}) + Fintype.card (Option {v // v ∈ Sᶜ})=n+2 := by
        simp only [Fintype.card_option,Fintype.card_coe]
        have hh := Finset.card_compl_add_card S
        omega
      change 2 * ((G.onSide S).faceCodimension (G.sideMarginal x S) + 2) ≤ _ at hb1
      change 2 * ((G.onSide Sᶜ).faceCodimension (G.sideMarginal x Sᶜ) + 2) ≤ _ at hb2
      omega
    · have hb := G.faceCodimension_no_tight heven' hcut
      omega

theorem sharp_face_rank (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) {x : E → ℝ}
    (hx : x ∈ G.polytope) : G.faceCodimension x + 2 ≤ 3 * m := by
  by_cases hm1 : m = 1
  · have htwo : Fintype.card V = 2 := by omega
    have hb := faceCodimension_two G htwo x
    omega
  · have heven : Even (Fintype.card V) := by rw [hV]; exact even_two_mul m
    have hb := sharp_face_rank_aux (Fintype.card V) G rfl heven (by omega) x
      (G.polytope_subset_constraintPolytope hx)
    omega

end MatchingEntropyBounds.Refined

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter Module


namespace MatchingEntropyBounds.Refined

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

open LooplessGraph

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem continuous_lowerObjective (κ : ℝ) : Continuous (lowerObjective (E := E) κ) := by
  exact continuous_entropy.sub (continuous_const.mul (continuous_entropy.comp (by fun_prop)))

def objectiveLineD (κ : ℝ) (x v : E → ℝ) (t : ℝ) : ℝ :=
  entropyLineD x v t - κ * entropyLineD (fun e => 1-x e) (fun e => -v e) t

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem objective_line_eventually_hasDerivAt (κ : ℝ) (x v : E → ℝ)
    (hzero : ∀ e, x e = 0 → v e = 0) (hone : ∀ e, x e = 1 → v e = 0) :
    ∀ᶠ t : ℝ in 𝓝 0,
      HasDerivAt (fun t => lowerObjective κ (fun e => x e+t*v e))
        (objectiveLineD κ x v t) t := by
  have hbar : ∀ e, 1-x e=0 → -v e=0 := by
    intro e he
    rw [hone e (by linarith), neg_zero]
  filter_upwards [entropy_line_eventually_hasDerivAt x v hzero,
    entropy_line_eventually_hasDerivAt (fun e => 1-x e) (fun e => -v e) hbar]
    with t ht hb
  have he : (fun t => lowerObjective κ (fun e => x e+t*v e)) =
      (fun t => entropy (fun e => x e+t*v e) -
        κ * entropy (fun e => (1-x e)+t*(-v e))) := by
    funext t
    unfold lowerObjective complementEntropy
    congr 2
    congr 1
    funext e
    ring
  rw [he]
  exact ht.sub (hb.const_mul κ)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem objectiveLineD_hasDerivAt (κ : ℝ) (x v : E → ℝ)
    (hzero : ∀ e, x e = 0 → v e = 0) (hone : ∀ e, x e = 1 → v e = 0) :
    HasDerivAt (objectiveLineD κ x v)
      (-(∑ e, (v e)^2/x e) + κ*(∑ e, (v e)^2/(1-x e))) 0 := by
  have hbar : ∀ e, 1-x e=0 → -v e=0 := by
    intro e he
    rw [hone e (by linarith), neg_zero]
  have hd := (entropyLineD_hasDerivAt x v hzero).sub
    ((entropyLineD_hasDerivAt (fun e => 1-x e) (fun e => -v e) hbar).const_mul κ)
  exact hd.congr_deriv (by simp only [neg_sq]; ring)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem objective_second_variation (κ : ℝ) {A : Type uA} [Fintype A]
    (x v : E → ℝ) (hzero : ∀ e, x e=0 → v e=0) (hone : ∀ e, x e=1 → v e=0)
    {p : A → ℝ} (hp : p ∈ probabilitySimplex A) (a : A → ℝ)
    (hcenter : ∑ i, p i*a i=0) (c₀ c₁ : ℝ)
    (hlocal : IsLocalMax (fun t => lowerObjective κ (fun e => x e+t*v e) +
      c₀+t*c₁+t^2*(∑ i, p i*(a i)^2)-Real.log (partition p a t)) 0) :
    -(∑ e, (v e)^2/x e) + κ*(∑ e, (v e)^2/(1-x e)) +
      (∑ i, p i*(a i)^2) ≤ 0 := by
  have hf := objective_line_eventually_hasDerivAt κ x v hzero hone
  have hg : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt (fun t => Real.log (partition p a t))
      (partition (fun i => p i*a i) a t / partition p a t) t :=
    Filter.Eventually.of_forall (logPartition_hasDerivAt hp a)
  have hd := second_deriv_quadratic_adjustment (c₀ := c₀) (c₁ := c₁)
    (v := ∑ i, p i*(a i)^2) hf hg (objectiveLineD_hasDerivAt κ x v hzero hone)
    (logPartition_second hp a)
  have hc : ContinuousAt (fun t => lowerObjective κ (fun e => x e+t*v e) +
      c₀+t*c₁+t^2*(∑ i, p i*(a i)^2)-Real.log (partition p a t)) 0 := by
    apply ContinuousAt.sub
    · apply ContinuousAt.add
      · apply ContinuousAt.add
        · exact hf.self_of_nhds.continuousAt.add_const c₀
        · fun_prop
      · fun_prop
    · exact hg.self_of_nhds.continuousAt
  have hh := second_deriv_nonpos_of_local_max hlocal hc
  rw [hd.deriv, hcenter] at hh
  nlinarith

omit [Fintype V] [DecidableEq V] in

theorem matching_objective_second_variation (κ : ℝ) (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x)
    (hmax : ∀ y ∈ G.polytope, lowerObjective κ y-maxMatchingEntropy G y ≤
      lowerObjective κ x-maxMatchingEntropy G x)
    (u : E → ℝ) (c : ℝ) (hcenter : ∑ M, p M*linearScore G u c M=0) :
    -(∑ e, (G.mean (fun M => p M*linearScore G u c M) e)^2/x e) +
      κ*(∑ e, (G.mean (fun M => p M*linearScore G u c M) e)^2/(1-x e)) +
      (∑ M, p M*(linearScore G u c M)^2) ≤ 0 := by
  let a := linearScore G u c
  let v := G.mean (fun M => p M*a M)
  let c₀ := ∑ M, p M*Real.log (p M)
  let c₁ := ∑ M, (p M*a M)*Real.log (p M)
  have hzero : ∀ e, x e=0 → v e=0 := by
    rw [← hp.2]
    exact mean_score_support G hp.1 a
  have hone : ∀ e, x e=1 → v e=0 := by
    rw [← hp.2]
    exact mean_score_one G hp.1 a hcenter
  apply objective_second_variation κ x v hzero hone hp.1 a hcenter c₀ c₁
  filter_upwards [score_law_eventually_simplex hp.1 a hcenter] with t ht
  let r := fun M => p M+t*(p M*a M)
  have hr : r ∈ probabilitySimplex G.Matching := ht
  have hrmean : G.mean r=fun e => x e+t*v e := by
    change G.meanLinear (p+t • (fun M => p M*a M)) = _
    rw [map_add, map_smul]
    change G.mean p+t • v = _
    rw [hp.2]
    rfl
  have hdual := matching_entropy_dual_bound G hp hopt hr
    (fun M hM => by dsimp [r]; simp [hM]) u c t
  have hscore : (∑ M, r M*a M)=t*(∑ M, p M*(a M)^2) := by
    dsimp [r]
    simp_rw [add_mul, mul_assoc t, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hcenter, zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro M _
    ring
  have hlog : (∑ M, r M*Real.log (p M))=c₀+t*c₁ := by
    dsimp [r, c₀, c₁]
    simp_rw [add_mul, mul_assoc t, Finset.sum_add_distrib, ← Finset.mul_sum]
  change maxMatchingEntropy G (G.mean r) ≤
    Real.log (partition p a t) - (∑ M, r M*Real.log (p M)) - t*(∑ M, r M*a M) at hdual
  rw [hlog, hscore] at hdual
  have hmaxr := hmax (G.mean r) (G.mean_mem_polytope hr)
  have hpart := partition_zero hp.1 a
  simp only [zero_mul, zero_pow (by omega : 2 ≠ 0), add_zero, hpart,
    Real.log_one, sub_zero]
  rw [← hopt, entropy_eq p] at hmaxr
  rw [← hrmean]
  dsimp only [c₀] at *
  nlinarith

theorem objectiveDefect_attains_max (κ : ℝ) (G : LooplessGraph V E)
    (heven : Even (Fintype.card V)) (hPM : Nonempty G.Matching) :
    ∃ x ∈ G.polytope, ∀ y ∈ G.polytope,
      lowerObjective κ y-maxMatchingEntropy G y ≤ lowerObjective κ x-maxMatchingEntropy G x := by
  have hs : UpperSemicontinuousOn (fun y => lowerObjective κ y-maxMatchingEntropy G y)
      G.polytope := by
    simpa only [sub_eq_add_neg, Pi.neg_apply] using
      (continuous_lowerObjective κ).continuousOn.upperSemicontinuousOn.add
        (maxMatchingEntropy_lowerSemicontinuousOn G heven).neg
  have hn : G.polytope.Nonempty := by
    obtain ⟨M⟩ := hPM
    exact ⟨G.indicator M,subset_convexHull ℝ _ (Set.mem_range_self M)⟩
  exact UpperSemicontinuousOn.exists_isMaxOn hn G.compact_polytope hs

open Matrix
omit [Fintype V] [DecidableEq V] in

theorem matching_objective_covariance (κ : ℝ) (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x)
    (hmax : ∀ y ∈ G.polytope, lowerObjective κ y-maxMatchingEntropy G y ≤
      lowerObjective κ x-maxMatchingEntropy G x)
    (u : {e // 0 < x e} → ℝ) :
    u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) ≤
      ∑ e, (1-κ*x e.val/(1-x e.val))*((covariance p (matchingNormalized G x) *ᵥ u) e)^2 := by
  let w := matchingScoreWeights x u
  let c := ∑ e, w e*x e
  let a := linearScore G w c
  let v := G.mean (fun M => p M*a M)
  have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p,hp⟩
  have hcenter : ∑ M, p M*a M=0 := by
    dsimp only [a,c]
    rw [linearScore_expectation,hp.2,hp.1.2,mul_one,sub_self]
  have hh := matching_objective_second_variation κ G hp hopt hmax w c hcenter
  have hzero : ∀ e, ¬0 < x e → v e=0 := by
    intro e he
    have he0 : x e=0 := le_antisymm (le_of_not_gt he) (G.coordinate_mem_Icc hx e).1
    exact mean_score_support G hp.1 a e (by rw [hp.2,he0])
  have hnorm : (∑ e, (v e)^2/x e) =
      ∑ e, ((covariance p (matchingNormalized G x) *ᵥ u) e)^2 := by
    rw [sum_positive_support x _ (fun e he => by rw [hzero e he]; simp)]
    apply Finset.sum_congr rfl
    intro e _
    rw [matchingNormalized_mulVec G hp,div_pow,Real.sq_sqrt e.property.le]
  have hbar : (∑ e, (v e)^2/(1-x e)) =
      ∑ e, x e.val/(1-x e.val)*((covariance p (matchingNormalized G x) *ᵥ u) e)^2 := by
    rw [sum_positive_support x _ (fun e he => by rw [hzero e he]; simp)]
    apply Finset.sum_congr rfl
    intro e _
    rw [matchingNormalized_mulVec G hp,div_pow,Real.sq_sqrt e.property.le]
    change (v e.val)^2/(1-x e.val)=x e.val/(1-x e.val)*((v e.val)^2/x e.val)
    field_simp [ne_of_gt e.property]
  have hquad : (∑ M, p M*(a M)^2)=u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) := by
    rw [covariance_quadratic hp.1.1]
    apply Finset.sum_congr rfl
    intro M _
    rw [← matchingNormalized_score G x u M]
  change -(∑ e, (v e)^2/x e)+κ*(∑ e, (v e)^2/(1-x e))+(∑ M,p M*(a M)^2) ≤ 0 at hh
  rw [hnorm,hbar,hquad] at hh
  have heq : (∑ e, (1-κ*x e.val/(1-x e.val))*((covariance p (matchingNormalized G x) *ᵥ u) e)^2) =
      (∑ e, ((covariance p (matchingNormalized G x) *ᵥ u) e)^2)-
      κ*(∑ e, x e.val/(1-x e.val)*((covariance p (matchingNormalized G x) *ᵥ u) e)^2) := by
    simp_rw [sub_mul,one_mul,Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [heq]
  linarith

omit [Fintype V] in

theorem lowerObjective_forced (κ : ℝ) (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (e₀ : E) (he : x e₀=1) :
    lowerObjective κ (fun e : {e // G.RemainingEdge e₀ e} => x e.val)=lowerObjective κ x := by
  have hz : ∀ e, ¬G.RemainingEdge e₀ e →
      Real.negMulLog (x e)=0 ∧ Real.negMulLog (1-x e)=0 := by
    intro e h
    by_cases hneq : e=e₀
    · simp [hneq,he]
    · simp [G.forced_coordinate_zero hx e₀ he hneq h]
  unfold lowerObjective complementEntropy entropy
  rw [sum_subtype_supported _ _ (fun e h => (hz e h).1),
    sum_subtype_supported _ _ (fun e h => (hz e h).2)]

theorem objective_max_has_forced (κ : ℝ) (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hn : 0 < Fintype.card V) (hx : x ∈ G.polytope)
    (hκ : (2 - κ) * (Fintype.card V : ℝ) < 4)
    (hmax : ∀ y ∈ G.polytope, lowerObjective κ y - maxMatchingEntropy G y ≤
      lowerObjective κ x - maxMatchingEntropy G x) : ∃ e, x e = 1 := by
  by_contra hforced
  push Not at hforced
  obtain ⟨m, hm⟩ := heven
  have hV : Fintype.card V = 2 * m := by omega
  have hmpos : 0 < m := by omega
  have heven : Even (Fintype.card V) := ⟨m, hm⟩
  obtain ⟨p, hp, hopt⟩ := maxMatchingEntropy_attained G hx
  have hsecond := covariance_weighted_rank (covariance_posSemidef p (matchingNormalized G x))
    (fun e => 1 - κ * x e.val / (1 - x e.val)) (matching_objective_covariance κ G hp hopt hmax)
  have htrace : (∑ e : {e // 0 < x e}, (1 - κ * x e.val / (1 - x e.val)) *
      covariance p (matchingNormalized G x) e e) =
      Fintype.card {e // 0 < x e} - (κ + 1) * (m : ℝ) := by
    have he (e : {e // 0 < x e}) : (1 - κ * x e.val / (1 - x e.val)) *
        covariance p (matchingNormalized G x) e e = 1 - (κ + 1) * x e.val := by
      rw [matching_covariance_diagonal G hp]
      have hh : 1 - x e.val ≠ 0 := sub_ne_zero.mpr (Ne.symm (hforced e.val))
      field_simp
      ring
    simp_rw [he]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hs : (∑ e : {e // 0 < x e}, x e.val) = (m : ℝ) := by
      rw [← G.marginal_sum hV hx]
      exact (sum_positive_support x x (fun e he =>
        le_antisymm (le_of_not_gt he) (G.coordinate_mem_Icc hx e).1)).symm
    rw [hs]
    simp
  rw [htrace] at hsecond
  have hrank := matching_covariance_rank_face G heven hp hopt
  have hsharp := sharp_face_rank G m hmpos hV hx
  have hrankR : (Fintype.card {e // 0 < x e} : ℝ) ≤ G.faceCodimension x +
      (covariance p (matchingNormalized G x)).rank := by exact_mod_cast hrank
  have hsharpR : (G.faceCodimension x : ℝ) + 2 ≤ 3 * (m : ℝ) := by exact_mod_cast hsharp
  rw [hV, Nat.cast_mul, Nat.cast_ofNat] at hκ
  nlinarith

theorem coefficient_down (κ : ℝ) {n k : ℕ} (hk : k ≤ n)
    (hn : (2 - κ) * (n : ℝ) < 4) : (2 - κ) * (k : ℝ) < 4 := by
  by_cases hc : 0 ≤ 2 - κ
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by exact_mod_cast hk) hc) hn
  · have hneg := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) (Nat.cast_nonneg k : (0:ℝ) ≤ k)
    linarith

theorem strict_lower_aux (κ : ℝ) (n : ℕ) :
    ∀ {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessGraph V E), Fintype.card V = n → Even n →
      (2 - κ) * (n : ℝ) < 4 →
      ∀ x ∈ G.polytope, lowerObjective κ x ≤ maxMatchingEntropy G x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V E _ _ _ _ G hcard heven hκ y hy
    by_cases hn : n = 0
    · have : IsEmpty V := Fintype.card_eq_zero_iff.mp (hcard.trans hn)
      have : IsEmpty E := ⟨fun e => isEmptyElim (G.left e)⟩
      simpa [lowerObjective, complementEntropy, entropy] using maxMatchingEntropy_nonneg G hy
    · have heven' : Even (Fintype.card V) := hcard ▸ heven
      have hPM : Nonempty G.Matching := by
        obtain ⟨p,hp⟩ := (G.mem_polytope_iff y).mp hy
        by_contra h
        have : IsEmpty G.Matching := not_nonempty_iff.mp h
        simpa using hp.1.2
      obtain ⟨x, hx, hmax⟩ := objectiveDefect_attains_max κ G heven' hPM
      obtain ⟨e₀, he₀⟩ := objective_max_has_forced κ G heven' (by omega) hx (hcard ▸ hκ) hmax
      have hc := G.remaining_vertex_card e₀
      have hlt : Fintype.card {v // G.RemainingVertex e₀ v} < n := by omega
      have hev : Even (Fintype.card {v // G.RemainingVertex e₀ v}) := by
        obtain ⟨r,hr⟩ := heven
        refine ⟨r-1,?_⟩
        omega
      obtain ⟨p,hp⟩ := (G.mem_polytope_iff x).mp hx
      have hs := G.forcedLaw_feasible hp e₀ he₀
      have hxr := ((G.deleteEndpoints e₀).mem_polytope_iff _).mpr ⟨_,hs⟩
      have hsmall := ih _ hlt (G.deleteEndpoints e₀) rfl hev (coefficient_down κ hlt.le hκ) _ hxr
      rw [lowerObjective_forced κ G hx e₀ he₀] at hsmall
      have hxbound := hsmall.trans (G.maxMatchingEntropy_forced_le hx e₀ he₀)
      have hcompare := hmax y hy
      linarith

theorem refined_lower (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) (x : E → ℝ) (hx : x ∈ G.polytope) :
    lowerObjective (2 - 2 / (m : ℝ)) x ≤ maxMatchingEntropy G x := by
  let c : ℝ := 2 - 2 / (m : ℝ)
  have hcont : Continuous (fun κ : ℝ => lowerObjective κ x) := by
    unfold lowerObjective
    fun_prop
  apply le_of_tendsto (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
    Tendsto (fun κ : ℝ => lowerObjective κ x) (𝓝[>] c) (𝓝 (lowerObjective c x)))
  filter_upwards [self_mem_nhdsWithin] with κ hκ
  have hκc : c < κ := hκ
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : (2 - c) * (2 * (m : ℝ)) = 4 := by
    dsimp [c]
    field_simp
    ring
  have hstrict : (2 - κ) * (Fintype.card V : ℝ) < 4 := by
    rw [hV, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [mul_lt_mul_of_pos_right hκc (by positivity : 0 < 2 * (m : ℝ))]
  exact strict_lower_aux κ (Fintype.card V) G rfl (by rw [hV]; exact even_two_mul m) hstrict x hx

def matchingProduct (G : LooplessGraph V E) (x : E → ℝ) (M : G.Matching) : ℝ :=
  ∏ e ∈ M.val, x e

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem matchingProduct_nonneg (G : LooplessGraph V E) {x : E → ℝ}
    (hx : ∀ e, 0 ≤ x e) (M : G.Matching) : 0 ≤ matchingProduct G x M :=
  Finset.prod_nonneg (fun e _ => hx e)

omit [Fintype V] [Fintype E] in
theorem matchingProduct_addForced (G : LooplessGraph V E) (x : E → ℝ) (e₀ : E)
    (N : (G.deleteEndpoints e₀).Matching) :
    matchingProduct G x (G.addForced e₀ N) =
      x e₀ * matchingProduct (G.deleteEndpoints e₀) (fun e => x e.val) N := by
  have hnot : e₀ ∉ N.val.image Subtype.val := by
    rintro h
    obtain ⟨e, _, he⟩ := Finset.mem_image.mp h
    exact G.remainingEdge_ne e₀ e.property he
  change (∏ e ∈ insert e₀ (N.val.image Subtype.val), x e) = _
  rw [Finset.prod_insert hnot, Finset.prod_image (fun _ _ _ _ h => Subtype.ext h)]
  rfl

omit [Fintype V] in
theorem sum_matching_incident (G : LooplessGraph V E) (w : G.Matching → ℝ) (v : V) :
    (∑ M, w M) = ∑ e, if G.Incident v e then ∑ M : {M : G.Matching // e ∈ M.val}, w M.val else 0 := by
  have hone (M : G.Matching) : (∑ e, if G.Incident v e ∧ e ∈ M.val then w M else 0) = w M := by
    obtain ⟨e, ⟨he, hev⟩, huniq⟩ := M.property v
    rw [Finset.sum_eq_single e]
    · simp [he, hev]
    · intro f _ hne
      have hf : ¬ (G.Incident v f ∧ f ∈ M.val) := by
        rintro ⟨hfv, hfM⟩
        exact hne (huniq f ⟨hfM, hfv⟩)
      simp [hf]
    · simp
  calc
    _ = ∑ M, ∑ e, if G.Incident v e ∧ e ∈ M.val then w M else 0 := by simp_rw [hone]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : G.Incident v e
      · simp only [he, true_and, ite_true]
        have hh := (sum_subtype_supported (fun M : G.Matching => e ∈ M.val)
          (fun M => if e ∈ M.val then w M else 0) (by intro M h; simp [h])).symm
        apply hh.trans
        apply Finset.sum_congr rfl
        intro M _
        exact ite_eq_left M.property
      · simp [he]

omit [Fintype V] in
theorem matchingProduct_recursion (G : LooplessGraph V E) (x : E → ℝ) (v : V) :
    (∑ M, matchingProduct G x M) =
      ∑ e, if G.Incident v e then x e *
        ∑ N, matchingProduct (G.deleteEndpoints e) (fun f => x f.val) N else 0 := by
  rw [sum_matching_incident G _ v]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : G.Incident v e
  · simp only [he, ite_true]
    rw [← (G.forcedMatchingEquiv e).sum_comp (fun M => matchingProduct G x M.val)]
    change (∑ N, matchingProduct G x (G.addForced e N)) = _
    simp_rw [matchingProduct_addForced]
    rw [Finset.mul_sum]
  · simp [he]

omit [Fintype V] [DecidableEq E] in
theorem degree_deleteEndpoints_le (G : LooplessGraph V E) {x : E → ℝ}
    (hx : ∀ e, 0 ≤ x e) (e₀ : E) (v : {v // G.RemainingVertex e₀ v}) :
    (G.deleteEndpoints e₀).degree (fun e => x e.val) v ≤ G.degree x v.val := by
  simp only [degree, deleteEndpoints_incident]
  rw [← Finset.sum_subtype (Finset.univ.filter (G.RemainingEdge e₀)) (by simp)
    (fun e => if G.Incident v.val e then x e else 0)]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro e _ _
  split
  · exact hx e
  · exact le_rfl

theorem matchingProduct_sum_le_aux (n : ℕ) :
    ∀ {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessGraph V E), Fintype.card V = n →
      ∀ x : E → ℝ, (∀ e, 0 ≤ x e) → (∀ v, G.degree x v ≤ 1) →
      (∑ M, matchingProduct G x M) ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V E _ _ _ _ G hcard x hx hd
    by_cases hn : n = 0
    · have : IsEmpty V := Fintype.card_eq_zero_iff.mp (hcard.trans hn)
      have : IsEmpty E := ⟨fun e => isEmptyElim (G.left e)⟩
      have hM : Fintype.card G.Matching ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr inferInstance
      have heach (M : G.Matching) : matchingProduct G x M = 1 := by
        rw [matchingProduct, Finset.eq_empty_of_isEmpty M.val, Finset.prod_empty]
      simp_rw [heach]
      simpa using (show (Fintype.card G.Matching : ℝ) ≤ 1 by exact_mod_cast hM)
    · have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      obtain ⟨v⟩ := this
      rw [matchingProduct_recursion G x v]
      calc
        _ ≤ ∑ e, if G.Incident v e then x e else 0 := by
          apply Finset.sum_le_sum
          intro e _
          split
          · have hc := G.remaining_vertex_card e
            have hlt : Fintype.card {v // G.RemainingVertex e v} < n := by omega
            have hb := ih _ hlt (G.deleteEndpoints e) rfl (fun f => x f.val)
              (fun f => hx f.val) (fun v => (degree_deleteEndpoints_le G hx e v).trans (hd v.val))
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (hx e)
          · exact le_rfl
        _ ≤ 1 := hd v

theorem matchingProduct_sum_le (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    (∑ M, matchingProduct G x M) ≤ 1 := by
  have hc := G.polytope_subset_constraintPolytope hx
  exact matchingProduct_sum_le_aux (Fintype.card V) G rfl x hc.1 (fun v => (hc.2.1 v).le)

theorem matching_entropy_le_F (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) : entropy p ≤ entropy x := by
  have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p, hp⟩
  have hfactor (M : G.Matching) (hM : 0 < p M) (e : E) (he : e ∈ M.val) : 0 < x e := by
    simpa [LooplessGraph.matchingBits, he] using matching_boolean_factor_pos G hp hM e
  have hprod (M : G.Matching) (hM : 0 < p M) : 0 < matchingProduct G x M :=
    Finset.prod_pos (fun e he => hfactor M hM e he)
  have hcross := entropy_le_subprob_crossEntropy
    (fun M => matchingProduct_nonneg G (fun e => (G.coordinate_mem_Icc hx e).1) M)
    (matchingProduct_sum_le G hx) hp.1
    (fun M hzero => le_antisymm (le_of_not_gt (fun hM => (ne_of_gt (hprod M hM)) hzero)) (hp.1.1 M))
  have hlog (M : G.Matching) : p M * Real.log (matchingProduct G x M) =
      ∑ e, (p M * G.indicator M e) * Real.log (x e) := by
    by_cases hzero : p M = 0
    · simp [hzero]
    · have hpos : 0 < p M := lt_of_le_of_ne (hp.1.1 M) (Ne.symm hzero)
      rw [matchingProduct, Real.log_prod (fun e he => ne_of_gt (hfactor M hpos e he)), Finset.mul_sum]
      simp only [LooplessGraph.indicator, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
      rw [← Finset.sum_filter]
      simp
  have heq : -(∑ M, p M * Real.log (matchingProduct G x M)) = entropy x := by
    simp_rw [hlog]
    rw [Finset.sum_comm, entropy_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    rw [← Finset.sum_mul]
    have he : (∑ M, p M * G.indicator M e) = x e := congrFun hp.2 e
    rw [he]
  rwa [heq] at hcross

theorem refined_upper (G : LooplessGraph V E) (x : E → ℝ) (hx : x ∈ G.polytope) :
    maxMatchingEntropy G x ≤ entropy x := by
  obtain ⟨p, hp, hopt⟩ := maxMatchingEntropy_attained G hx
  rw [← hopt]
  exact matching_entropy_le_F G hp

end MatchingEntropyBounds.Refined

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter Module Matrix


namespace MatchingEntropyBounds.Refined

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

open LooplessGraph

theorem pointwise_entropy_oai (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) (hPM : Nonempty G.Matching)
    (x : E → ℝ) (hx : x ∈ G.polytope) :
    entropy x - (2 - 2 / (m : ℝ)) * complementEntropy x ≤ maxMatchingEntropy G x ∧
      maxMatchingEntropy G x ≤ entropy x := by
  obtain ⟨_⟩ := hPM
  exact ⟨refined_lower G m hm hV x hx, refined_upper G x hx⟩

omit [Fintype V] [DecidableEq V] in
theorem F_nonneg (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    0 ≤ entropy x := by
  exact Finset.sum_nonneg (fun e _ => Real.negMulLog_nonneg
    (G.coordinate_mem_Icc hx e).1 (G.coordinate_mem_Icc hx e).2)

omit [Fintype V] [DecidableEq V] in
theorem B_nonneg (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    0 ≤ complementEntropy x := by
  apply Finset.sum_nonneg
  intro e _
  exact Real.negMulLog_nonneg (sub_nonneg.mpr (G.coordinate_mem_Icc hx e).2)
    (by linarith [(G.coordinate_mem_Icc hx e).1])

theorem B_le_order (G : LooplessGraph V E) (m : ℕ) (hV : Fintype.card V = 2 * m)
    {x : E → ℝ} (hx : x ∈ G.polytope) : complementEntropy x ≤ m := by
  rw [← G.marginal_sum hV hx]
  apply Finset.sum_le_sum
  intro e _
  simpa only [sub_sub_cancel] using
    Real.negMulLog_le_one_sub_self (sub_nonneg.mpr (G.coordinate_mem_Icc hx e).2)

theorem entropy_defect (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) (hPM : Nonempty G.Matching)
    (x : E → ℝ) (hx : x ∈ G.polytope) :
    0 ≤ entropy x - maxMatchingEntropy G x ∧
      entropy x - maxMatchingEntropy G x ≤ min (entropy x) (2 * (m : ℝ) - 2) := by
  have hb := pointwise_entropy_oai G m hm hV hPM x hx
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc : 0 ≤ 2 - 2 / (m : ℝ) := by
    have hd : 2 / (m : ℝ) ≤ 2 := (div_le_iff₀ hmR).mpr (by linarith)
    linarith
  have heq : (2 - 2 / (m : ℝ)) * m = 2 * (m : ℝ) - 2 := by field_simp
  have hB := mul_le_mul_of_nonneg_left (B_le_order G m hV hx) hc
  rw [heq] at hB
  refine ⟨sub_nonneg.mpr hb.2, le_min ?_ ?_⟩
  · linarith [maxMatchingEntropy_nonneg G hx]
  · linarith [hb.1]

section UniformLaw
variable {I : Type uI} [Fintype I]

def uniformLaw (I : Type uI) [Fintype I] : I → ℝ := fun _ => (Fintype.card I : ℝ)⁻¹

theorem uniformLaw_simplex [Nonempty I] : uniformLaw I ∈ probabilitySimplex I := by
  have hN : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨fun _ => inv_nonneg.mpr (Nat.cast_nonneg _), ?_⟩
  simp [uniformLaw, hN]

theorem uniformLaw_entropy [Nonempty I] : entropy (uniformLaw I) = Real.log (Fintype.card I : ℝ) := by
  have hN : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [entropy, uniformLaw, Real.negMulLog, Real.log_inv, neg_mul_neg,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
end UniformLaw

omit [Fintype V] [DecidableEq V] in
theorem uniformMatching_mean (G : LooplessGraph V E) (hPM : Nonempty G.Matching) :
    ∃ z ∈ G.polytope, maxMatchingEntropy G z = Real.log (Fintype.card G.Matching : ℝ) := by
  let := hPM
  have hp := uniformLaw_simplex (I := G.Matching)
  have hz : G.mean (uniformLaw G.Matching) ∈ G.polytope := G.mean_mem_polytope hp
  refine ⟨_, hz, le_antisymm (maxMatchingEntropy_le_log_card G hz) ?_⟩
  rw [← uniformLaw_entropy (I := G.Matching)]
  exact entropy_le_maxMatchingEntropy G ⟨hp, rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem continuous_binaryEntropy : Continuous (binaryEntropy (E := E)) := by
  exact continuous_entropy.add (continuous_entropy.comp (by fun_prop))

theorem optimized_entropy (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) (hPM : Nonempty G.Matching) :
    ∃ x ∈ G.polytope, ∃ y ∈ G.polytope,
      (∀ z ∈ G.polytope, entropy z ≤ entropy x) ∧
      (∀ z ∈ G.polytope, binaryEntropy z ≤ binaryEntropy y) ∧
      Real.log (Fintype.card G.Matching : ℝ) ≤ entropy x ∧
      entropy x ≤ Real.log (Fintype.card G.Matching : ℝ) + 2 * (m : ℝ) - 2 ∧
      Real.log (Fintype.card G.Matching : ℝ) ≤ binaryEntropy y ∧
      binaryEntropy y ≤ Real.log (Fintype.card G.Matching : ℝ) + 3 * (m : ℝ) - 2 := by
  obtain ⟨z, hz, heq⟩ := uniformMatching_mean G hPM
  have hn : G.polytope.Nonempty := ⟨z, hz⟩
  obtain ⟨x, hx, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn hn G.compact_polytope
    continuous_entropy.continuousOn.upperSemicontinuousOn
  obtain ⟨y, hy, hmaxb⟩ := UpperSemicontinuousOn.exists_isMaxOn hn G.compact_polytope
    continuous_binaryEntropy.continuousOn.upperSemicontinuousOn
  have hxdef := (entropy_defect G m hm hV hPM x hx).2.trans (min_le_right _ _)
  have hydef := (entropy_defect G m hm hV hPM y hy).2.trans (min_le_right _ _)
  have hxu := maxMatchingEntropy_le_log_card G hx
  have hyu := maxMatchingEntropy_le_log_card G hy
  have hzu := refined_upper G z hz
  have hzB := B_nonneg G hz
  have hyB := B_le_order G m hV hy
  have hzx : entropy z ≤ entropy x := hmax hz
  have hzy := hmaxb hz
  change entropy z + complementEntropy z ≤ entropy y + complementEntropy y at hzy
  refine ⟨x, hx, y, hy, hmax, hmaxb, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · change _ ≤ entropy y + complementEntropy y
    linarith
  · change entropy y + complementEntropy y ≤ _
    linarith

def countBound (m k : ℕ) (N : ℝ) : Prop :=
  (k = 1 → 1 ≤ N) ∧
  (2 ≤ k → (k : ℝ)^m * (1 - 1 / (k : ℝ))^(2 * (m - 1) * (k - 1)) ≤ N ∧
    Real.exp (-2 * ((m : ℝ) - 1)) * (k : ℝ)^m ≤
      (k : ℝ)^m * (1 - 1 / (k : ℝ))^(2 * (m - 1) * (k - 1)) ∧
    (Real.exp (-2) * (k : ℝ))^m ≤ Real.exp (-2 * ((m : ℝ) - 1)) * (k : ℝ)^m)

omit [Fintype V] [DecidableEq V] in
theorem matching_nonempty_of_mem (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    Nonempty G.Matching := by
  obtain ⟨p, hp⟩ := (G.mem_polytope_iff x).mp hx
  by_contra h
  have : IsEmpty G.Matching := not_nonempty_iff.mp h
  simpa using hp.1.2

theorem entropy_uniform (G : LooplessGraph V E) {m k : ℕ}
    (hV : Fintype.card V = 2 * m) (hk : 2 ≤ k) {x : E → ℝ} (hx : x ∈ G.polytope)
    (hu : ∀ e, x e = 0 ∨ x e = 1 / (k : ℝ)) :
    entropy x = (m : ℝ) * Real.log (k : ℝ) ∧
    complementEntropy x = -(m : ℝ) * ((k : ℝ) - 1) * Real.log (1 - 1 / (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ha (e : E) : Real.negMulLog (x e) = x e * Real.log (k : ℝ) := by
    rcases hu e with he | he
    · simp [he]
    · rw [he, one_div, Real.negMulLog, Real.log_inv]; ring
  have hb (e : E) : Real.negMulLog (1 - x e) =
      -((k : ℝ) - 1) * x e * Real.log (1 - 1 / (k : ℝ)) := by
    rcases hu e with he | he
    · simp [he]
    · rw [he, Real.negMulLog]; field_simp
  constructor
  · simp_rw [entropy, ha]
    rw [← Finset.sum_mul, G.marginal_sum hV hx]
  · simp_rw [complementEntropy, entropy, hb]
    rw [← Finset.sum_mul, ← Finset.mul_sum, G.marginal_sum hV hx]
    ring

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem finiteCount_eq_exp {m k : ℕ} (hm : 0 < m) (hk : 2 ≤ k) :
    (k : ℝ)^m * (1 - 1 / (k : ℝ))^(2 * (m - 1) * (k - 1)) =
      Real.exp ((m : ℝ) * Real.log (k : ℝ) +
        2 * ((m : ℝ) - 1) * ((k : ℝ) - 1) * Real.log (1 - 1 / (k : ℝ))) := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  have ht : 0 < 1 - 1 / (k : ℝ) := sub_pos.mpr ((div_lt_one (by linarith)).mpr hkR)
  have hc : 2 * ((m : ℝ) - 1) * ((k : ℝ) - 1) = ((2 * (m - 1) * (k - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num
  rw [hc, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by linarith), Real.exp_log ht]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem log_uniform_loss {k : ℕ} (hk : 2 ≤ k) :
    -1 ≤ ((k : ℝ) - 1) * Real.log (1 - 1 / (k : ℝ)) := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have ht : 0 < 1 - 1 / (k : ℝ) := sub_pos.mpr ((div_lt_one hk0).mpr hkR)
  have hb := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
  rw [Real.log_inv] at hb
  have hkm : 0 < (k : ℝ) - 1 := by linarith
  have heq : ((1 - 1 / (k : ℝ))⁻¹ - 1) * ((k : ℝ) - 1) = 1 := by
    field_simp; ring
  have hh := mul_le_mul_of_nonneg_right hb (by linarith : 0 ≤ (k : ℝ) - 1)
  rw [heq] at hh
  nlinarith

theorem refined_uniform_count (G : LooplessGraph V E) {m k : ℕ}
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) {x : E → ℝ} (hx : x ∈ G.polytope)
    (hu : ∀ e, x e = 0 ∨ x e = 1 / (k : ℝ)) :
    countBound m k (Fintype.card G.Matching : ℝ) := by
  have hPM := matching_nonempty_of_mem G hx
  have hN : (0 : ℝ) < Fintype.card G.Matching := by
    exact_mod_cast Fintype.card_pos_iff.mpr hPM
  refine ⟨fun _ => by exact_mod_cast Fintype.card_pos_iff.mpr hPM, fun hk => ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨hF, hB⟩ := entropy_uniform G hV hk hx hu
  have hl := (pointwise_entropy_oai G m hm hV hPM x hx).1.trans (maxMatchingEntropy_le_log_card G hx)
  rw [hF, hB] at hl
  have hl' : (m : ℝ) * Real.log (k : ℝ) +
      2 * ((m : ℝ) - 1) * ((k : ℝ) - 1) * Real.log (1 - 1 / (k : ℝ)) ≤
      Real.log (Fintype.card G.Matching : ℝ) := by
    refine Eq.trans_le ?_ hl
    have hmm : (2 : ℝ) / m * m = 2 := div_mul_cancel₀ 2 hm0.ne'
    linear_combination (((k : ℝ) - 1) * Real.log (1 - 1 / (k : ℝ))) * hmm
  refine ⟨?_, ?_, ?_⟩
  · rw [finiteCount_eq_exp hm hk]
    simpa only [Real.exp_log hN] using Real.exp_le_exp.mpr hl'
  · rw [finiteCount_eq_exp hm hk]
    have heq : Real.exp (-2 * ((m : ℝ) - 1)) * (k : ℝ)^m =
        Real.exp (-2 * ((m : ℝ) - 1) + (m : ℝ) * Real.log (k : ℝ)) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hk0]
    rw [heq]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (log_uniform_loss hk) (by linarith : 0 ≤ 2 * ((m : ℝ) - 1))
    nlinarith
  · rw [mul_pow, ← Real.exp_nat_mul]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hk0.le _)
    apply Real.exp_le_exp.mpr
    linarith

theorem structural_count (G : LooplessGraph V E) (m k : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) (hk : 1 ≤ k)
    (M : Fin k → G.Matching)
    (hd : ∀ i j, i ≠ j → Disjoint (M i).val (M j).val) :
    countBound m k (Fintype.card G.Matching : ℝ) := by
  obtain ⟨x, hx, hu⟩ := selected_uniform_mean G hk M hd
  exact refined_uniform_count G hm hV hx hu

theorem regular_count (G : LooplessGraph V E) (m k : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) (hk : 1 ≤ k)
    (hregular : ∀ v, (Finset.univ.filter (G.Incident v)).card = k)
    (hodd : ∀ S : Finset V, Odd S.card → k ≤ (G.cut S).card) :
    countBound m k (Fintype.card G.Matching : ℝ) := by
  exact refined_uniform_count G hm hV (regular_uniform_mem G hV hk hregular hodd) (fun _ => Or.inr rfl)

omit [Fintype V] [DecidableEq E] in

theorem degree_cut_count (G : LooplessGraph V E) {k : ℕ}
    (hreg : ∀ v, (Finset.univ.filter (G.Incident v)).card = k) (S : Finset V) :
    S.card * k = 2 * (Finset.univ.filter (fun e => G.left e ∈ S ∧ G.right e ∈ S)).card +
      (G.cut S).card := by
  classical
  have hp (e : E) : ((if G.left e ∈ S then (1 : ℕ) else 0) +
      (if G.right e ∈ S then 1 else 0)) =
      2 * (if G.left e ∈ S ∧ G.right e ∈ S then 1 else 0) +
        (if G.Crosses S e then 1 else 0) := by
    by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S <;> simp [Crosses, hl, hr]
  calc
    S.card * k = ∑ v ∈ S, (∑ e : E, if G.Incident v e then (1 : ℕ) else 0) := by
      simp [Finset.sum_boole, hreg, Finset.sum_const]
    _ = ∑ e : E, ∑ v ∈ S, if G.Incident v e then (1 : ℕ) else 0 := Finset.sum_comm
    _ = _ := by
      simp_rw [G.incidence_sum, hp]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [Finset.sum_boole, cut]

omit [DecidableEq E] in

theorem connected_odd_cut (G : LooplessGraph V E) {m k : ℕ}
    (hV : Fintype.card V = 2 * m) (hk : 1 ≤ k)
    (hregular : ∀ v, (Finset.univ.filter (G.Incident v)).card = k)
    (hconn : ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → k - 1 ≤ (G.cut S).card)
    (S : Finset V) (hS : Odd S.card) : k ≤ (G.cut S).card := by
  have hsmod := Nat.odd_iff.mp hS
  have hn : S.Nonempty := Finset.card_pos.mp (by omega)
  have hp : S ≠ Finset.univ := by
    intro hh
    simp only [hh, Finset.card_univ, hV] at hsmod
    omega
  have hc := hconn S hn hp
  have heq := congrArg (fun a : ℕ => a % 2) (degree_cut_count G hregular S)
  rw [Nat.mul_mod S.card k 2, hsmod] at heq
  simp only [one_mul, Nat.mod_mod] at heq
  omega

theorem connected_regular_count (G : LooplessGraph V E) (m k : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) (hk : 1 ≤ k)
    (hregular : ∀ v, (Finset.univ.filter (G.Incident v)).card = k)
    (hconn : ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → k - 1 ≤ (G.cut S).card) :
    countBound m k (Fintype.card G.Matching : ℝ) := by
  exact regular_count G m k hm hV hk hregular (connected_odd_cut G hV hk hregular hconn)

def weightedPartition (G : LooplessGraph V E) (β : E → ℝ) : ℝ :=
  ∑ M : G.Matching, (2 : ℝ) ^ (∑ e, β e * G.indicator M e)
def weightedObjective (β x : E → ℝ) : ℝ := entropy x / Real.log 2 + ∑ e, β e * x e

def gibbsLaw (G : LooplessGraph V E) (β : E → ℝ) (M : G.Matching) : ℝ :=
  (2 : ℝ) ^ (∑ e, β e * G.indicator M e) / weightedPartition G β

omit [Fintype V] [DecidableEq V] in
theorem weightedPartition_pos (G : LooplessGraph V E) (hPM : Nonempty G.Matching) (β : E → ℝ) :
    0 < weightedPartition G β := by
  let := hPM
  exact Finset.sum_pos (fun M _ => Real.rpow_pos_of_pos (by norm_num) _) Finset.univ_nonempty

omit [Fintype V] [DecidableEq V] in
theorem gibbsLaw_pos (G : LooplessGraph V E) (hPM : Nonempty G.Matching) (β : E → ℝ) (M : G.Matching) :
    0 < gibbsLaw G β M :=
  div_pos (Real.rpow_pos_of_pos (by norm_num) _) (weightedPartition_pos G hPM β)

omit [Fintype V] [DecidableEq V] in
theorem gibbsLaw_simplex (G : LooplessGraph V E) (hPM : Nonempty G.Matching) (β : E → ℝ) :
    gibbsLaw G β ∈ probabilitySimplex G.Matching := by
  refine ⟨fun M => (gibbsLaw_pos G hPM β M).le, ?_⟩
  simp only [gibbsLaw, ← Finset.sum_div]
  exact div_self (weightedPartition_pos G hPM β).ne'

omit [Fintype V] [DecidableEq V] in
theorem gibbs_cross_entropy (G : LooplessGraph V E) (hPM : Nonempty G.Matching) (β : E → ℝ)
    {p : G.Matching → ℝ} (hp : p ∈ probabilitySimplex G.Matching) :
    -(∑ M, p M * Real.log (gibbsLaw G β M)) =
      Real.log (weightedPartition G β) - Real.log 2 * (∑ e, β e * G.mean p e) := by
  have hl (M : G.Matching) : Real.log (gibbsLaw G β M) =
      (∑ e, β e * G.indicator M e) * Real.log 2 - Real.log (weightedPartition G β) := by
    rw [gibbsLaw, Real.log_div (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _))
      (weightedPartition_pos G hPM β).ne', Real.log_rpow (by norm_num)]
  simp_rw [hl, mul_sub, ← mul_assoc]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hp.2, one_mul, sum_mean_assoc]
  ring

omit [Fintype V] [DecidableEq V] in
theorem gibbs_law_bound (G : LooplessGraph V E) (hPM : Nonempty G.Matching) (β : E → ℝ)
    {p : G.Matching → ℝ} (hp : p ∈ probabilitySimplex G.Matching) :
    entropy p / Real.log 2 + (∑ e, β e * G.mean p e) ≤
      Real.log (weightedPartition G β) / Real.log 2 := by
  have h := entropy_le_crossEntropy (gibbsLaw_simplex G hPM β) hp
    (fun M hzero => ((gibbsLaw_pos G hPM β M).ne' hzero).elim)
  rw [gibbs_cross_entropy G hPM β hp] at h
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (le_div_iff₀ hlog).mpr
  rw [add_mul, div_mul_cancel₀ _ hlog.ne']
  nlinarith

omit [Fintype V] [DecidableEq V] in
theorem gibbs_law_equality (G : LooplessGraph V E) (hPM : Nonempty G.Matching) (β : E → ℝ) :
    entropy (gibbsLaw G β) / Real.log 2 + (∑ e, β e * G.mean (gibbsLaw G β) e) =
      Real.log (weightedPartition G β) / Real.log 2 := by
  have h := gibbs_cross_entropy G hPM β (gibbsLaw_simplex G hPM β)
  rw [← entropy_eq] at h
  rw [h]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp
  ring

omit [Fintype V] [DecidableEq V] in

theorem gibbs_variational (G : LooplessGraph V E) (hPM : Nonempty G.Matching) (β : E → ℝ) :
    gibbsLaw G β ∈ probabilitySimplex G.Matching ∧
    maxMatchingEntropy G (G.mean (gibbsLaw G β)) / Real.log 2 +
        (∑ e, β e * G.mean (gibbsLaw G β) e) = Real.log (weightedPartition G β) / Real.log 2 ∧
    ∀ x ∈ G.polytope, maxMatchingEntropy G x / Real.log 2 + (∑ e, β e * x e) ≤
      Real.log (weightedPartition G β) / Real.log 2 := by
  have hp := gibbsLaw_simplex G hPM β
  have hx := G.mean_mem_polytope hp
  have hu : ∀ x ∈ G.polytope, maxMatchingEntropy G x / Real.log 2 + (∑ e, β e * x e) ≤
      Real.log (weightedPartition G β) / Real.log 2 := by
    intro x hx
    obtain ⟨p, hp, hopt⟩ := maxMatchingEntropy_attained G hx
    rw [← hopt, ← hp.2]
    exact gibbs_law_bound G hPM β hp.1
  refine ⟨hp, le_antisymm (hu _ hx) ?_, hu⟩
  rw [← gibbs_law_equality G hPM β]
  exact add_le_add (div_le_div_of_nonneg_right (entropy_le_maxMatchingEntropy G ⟨hp, rfl⟩)
    (Real.log_pos (by norm_num)).le) le_rfl

theorem weighted_count (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) (hPM : Nonempty G.Matching)
    (β : E → ℝ) :
    ∃ x ∈ G.polytope, (∀ y ∈ G.polytope, weightedObjective β y ≤ weightedObjective β x) ∧
      weightedObjective β x - (2 * (m : ℝ) - 2) / Real.log 2 ≤
        Real.log (weightedPartition G β) / Real.log 2 ∧
      Real.log (weightedPartition G β) / Real.log 2 ≤ weightedObjective β x := by
  obtain ⟨hp, heq, hu⟩ := gibbs_variational G hPM β
  have hz := G.mean_mem_polytope hp
  have hcont : Continuous (weightedObjective β) := by
    unfold weightedObjective
    exact (continuous_entropy.div_const _).add (by fun_prop)
  obtain ⟨x, hx, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn ⟨_, hz⟩ G.compact_polytope
    hcont.continuousOn.upperSemicontinuousOn
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨x, hx, hmax, ?_, ?_⟩
  · have hd := (entropy_defect G m hm hV hPM x hx).2.trans (min_le_right _ _)
    have hd' := div_le_div_of_nonneg_right hd hlog.le
    have huu := hu x hx
    dsimp only [weightedObjective]
    rw [sub_div] at hd'
    linarith
  · rw [← heq]
    apply le_trans _ (hmax hz)
    exact add_le_add (div_le_div_of_nonneg_right (refined_upper G _ hz) hlog.le) le_rfl

end MatchingEntropyBounds.Refined

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds.Refined

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def minimalFace (G : LooplessGraph V E) (x : E → ℝ) : Set (E → ℝ) :=
  {y | y ∈ G.polytope ∧ (∀ e, x e = 0 → y e = 0) ∧
    ∀ S : Finset V, Odd S.card → G.cutMass x S = 1 → G.cutMass y S = 1}

def faceDimension (G : LooplessGraph V E) (x : E → ℝ) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (minimalFace G x)).direction

theorem even_of_mem (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    Even (Fintype.card V) := by
  obtain ⟨M⟩ := matching_nonempty_of_mem G hx
  rw [← G.matching_card_twice M]
  exact even_two_mul _

omit [Fintype V] in
theorem self_mem_minimalFace (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    x ∈ minimalFace G x := ⟨hx, fun _ h => h, fun _ _ h => h⟩

omit [Fintype V] in
theorem minimalFace_sub_direction (G : LooplessGraph V E) {x y : E → ℝ}
    (hx : x ∈ G.polytope) (hy : y ∈ minimalFace G x) :
    y - x ∈ (G.faceSpace x).map (LooplessGraph.positiveExtension x) := by
  let u : {e // 0 < x e} → ℝ := fun e => y e.val - x e.val
  have hext : LooplessGraph.positiveExtension x u = y - x := by
    ext e
    by_cases he : 0 < x e
    · simp [LooplessGraph.positiveExtension, he, u]
    · have hz : x e = 0 := le_antisymm (le_of_not_gt he) ((G.polytope_subset_constraintPolytope hx).1 e)
      simp [LooplessGraph.positiveExtension, hz, hy.2.1 e hz]
  refine ⟨u, ?_, hext⟩
  rw [LooplessGraph.faceSpace]
  change G.degreeLinear (LooplessGraph.positiveExtension x u) = 0 ∧ _
  rw [hext]
  constructor
  · rw [map_sub]
    ext v
    change G.degree y v - G.degree x v = 0
    rw [(G.polytope_subset_constraintPolytope hy.1).2.1,
      (G.polytope_subset_constraintPolytope hx).2.1, sub_self]
  · intro S hS ht
    rw [map_sub]
    change G.cutMass y S - G.cutMass x S = 0
    rw [hy.2.2 S hS ht, ht, sub_self]

theorem direction_eventually_minimalFace (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) {u : E → ℝ}
    (hu : u ∈ (G.faceSpace x).map (LooplessGraph.positiveExtension x)) :
    ∀ᶠ t : ℝ in 𝓝 0, x + t • u ∈ minimalFace G x := by
  obtain ⟨v, hv, rfl⟩ := hu
  have hline := G.faceSpace_eventually_line (G.polytope_subset_constraintPolytope hx) hv
  rw [← G.polytope_eq_constraints (even_of_mem G hx)] at hline
  filter_upwards [hline] with t ht
  refine ⟨ht, ?_, ?_⟩
  · intro e he
    simp [he, LooplessGraph.positiveExtension_zero x v he]
  · intro S hS hcut
    change G.cutLinear S (x + t • LooplessGraph.positiveExtension x v) = 1
    rw [map_add, map_smul, hv.2 S hS hcut, smul_zero, add_zero]
    exact hcut

theorem minimalFace_spec (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    x ∈ minimalFace G x ∧ Convex ℝ (minimalFace G x) ∧
    IsExtreme ℝ G.polytope (minimalFace G x) ∧
    ∀ A : Set (E → ℝ), IsExtreme ℝ G.polytope A → x ∈ A → minimalFace G x ⊆ A := by
  refine ⟨self_mem_minimalFace G hx, ?_, ?_, ?_⟩
  · intro y hy z hz a b ha hb hab
    refine ⟨(convex_convexHull ℝ _ ) hy.1 hz.1 ha hb hab, ?_, ?_⟩
    · intro e he
      simp [hy.2.1 e he, hz.2.1 e he]
    · intro S hS ht
      rw [G.cutMass_linear, hy.2.2 S hS ht, hz.2.2 S hS ht]
      simpa using hab
  · refine ⟨fun _ h => h.1, ?_⟩
    intro y hy z hz w hw hseg
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
    have hyc := G.polytope_subset_constraintPolytope hy
    have hzc := G.polytope_subset_constraintPolytope hz
    refine ⟨hy, ?_, ?_⟩
    · intro e he
      have h := hw.2.1 e he
      change a * y e + b * z e = 0 at h
      have hn := mul_nonneg hb.le (hzc.1 e)
      have hyn := hyc.1 e
      nlinarith
    · intro S hS ht
      have h := hw.2.2 S hS ht
      rw [G.cutMass_linear] at h
      have hyn := hyc.2.2 S hS
      have hzn := hzc.2.2 S hS
      nlinarith
  · intro A hA hxA y hy
    have hline := direction_eventually_minimalFace G hx (minimalFace_sub_direction G hx hy)
    have hneg : ∀ᶠ t : ℝ in 𝓝 0, x + (-t) • (y - x) ∈ minimalFace G x :=
      (show Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) by
        simpa using continuous_neg.tendsto (0 : ℝ)).eventually hline
    have hh : ∀ᶠ t : ℝ in 𝓝[>] 0, (x + (-t) • (y-x) ∈ minimalFace G x) ∧ 0 < t :=
      (hneg.filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
    obtain ⟨a, ha, ha0⟩ := hh.exists
    apply hA.left_mem_of_mem_openSegment hy.1 ha.1 hxA
    refine ⟨a / (1+a), 1 / (1+a), div_pos ha0 (by linarith),
      div_pos (by norm_num) (by linarith), ?_, ?_⟩
    · field_simp
      ring
    · ext e
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring

theorem minimalFace_direction (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    (affineSpan ℝ (minimalFace G x)).direction =
      (G.faceSpace x).map (LooplessGraph.positiveExtension x) := by
  apply le_antisymm
  · have hle : affineSpan ℝ (minimalFace G x) ≤
        AffineSubspace.mk' x ((G.faceSpace x).map (LooplessGraph.positiveExtension x)) := by
      apply affineSpan_le.mpr
      intro y hy
      exact (AffineSubspace.mem_mk').mpr (minimalFace_sub_direction G hx hy)
    simpa using AffineSubspace.direction_le hle
  · intro u hu
    have he := direction_eventually_minimalFace G hx hu
    have hh : ∀ᶠ t : ℝ in 𝓝[>] 0, (x + t • u ∈ minimalFace G x) ∧ 0 < t :=
      (he.filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
    obtain ⟨a, ha, ha0⟩ := hh.exists
    have hd := AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ _ ha) (subset_affineSpan ℝ _ (self_mem_minimalFace G hx))
    have hd' : a • u ∈ (affineSpan ℝ (minimalFace G x)).direction := by
      simpa using hd
    have hh := (affineSpan ℝ (minimalFace G x)).direction.smul_mem a⁻¹ hd'
    simpa [smul_smul, ne_of_gt ha0] using hh

omit [Fintype E] [DecidableEq E] in
theorem positiveExtension_injective (x : E → ℝ) :
    Function.Injective (LooplessGraph.positiveExtension x) := by
  intro u v h
  ext e
  simpa using congrFun h e.val

theorem faceDimension_eq (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    faceDimension G x = Module.finrank ℝ (G.faceSpace x) := by
  rw [faceDimension, minimalFace_direction G hx]
  exact (Submodule.equivMapOfInjective _ (positiveExtension_injective x) _).finrank_eq.symm

theorem minimalFace_rank (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) {x : E → ℝ} (hx : x ∈ G.polytope) :
    Fintype.card {e // 0 < x e} + 2 ≤ faceDimension G x + 3 * m := by
  have hr := sharp_face_rank G m hm hV hx
  have hd := (G.faceSpace x).finrank_quotient_add_finrank
  rw [Module.finrank_pi] at hd
  rw [faceDimension_eq G hx]
  dsimp only [LooplessGraph.faceCodimension] at hr
  omega

def IsFractional (x : E → ℝ) (e : E) : Prop := 0 < x e ∧ x e < 1

end MatchingEntropyBounds.Refined

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds.Refined

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def FractionalVertex (G : LooplessGraph V E) (x : E → ℝ) (v : V) : Prop :=
  ∃ e, IsFractional x e ∧ G.Incident v e

instance fractionalVertexDecidable (G : LooplessGraph V E) (x : E → ℝ) :
    DecidablePred (FractionalVertex G x) := Classical.decPred _
instance fractionalEdgeDecidable (x : E → ℝ) : DecidablePred (IsFractional x) := Classical.decPred _

def fractionalGraph (G : LooplessGraph V E) (x : E → ℝ) :
    LooplessGraph {v // FractionalVertex G x v} {e // IsFractional x e} where
  left e := ⟨G.left e.val, e.val, e.property, Or.inl rfl⟩
  right e := ⟨G.right e.val, e.val, e.property, Or.inr rfl⟩
  loopless e h := G.loopless e.val (congrArg Subtype.val h)

def fractionalMean (x : E → ℝ) (e : {e // IsFractional x e}) : ℝ := x e.val

def fractionalExtension (x : E → ℝ) : ({e // IsFractional x e} → ℝ) →ᵃ[ℝ] (E → ℝ) where
  toFun z e := if h : IsFractional x e then z ⟨e,h⟩ else x e
  linear := {
    toFun := fun u e => if h : IsFractional x e then u ⟨e,h⟩ else 0
    map_add' := by intro u v; ext e; by_cases h : IsFractional x e <;> simp [h]
    map_smul' := by intro a u; ext e; by_cases h : IsFractional x e <;> simp [h] }
  map_vadd' := by intro z u; ext e; by_cases h : IsFractional x e <;> simp [h]

def fixedFace (G : LooplessGraph V E) (x : E → ℝ) : Set (E → ℝ) :=
  {y | y ∈ G.polytope ∧ ∀ e, ¬IsFractional x e → y e = x e}

omit [Fintype E] [DecidableEq E] in
@[simp] theorem fractionalExtension_apply_fractional (x : E → ℝ)
    (z : {e // IsFractional x e} → ℝ) (e : {e // IsFractional x e}) :
    fractionalExtension x z e.val = z e := by simp [fractionalExtension, e.property]

omit [Fintype E] [DecidableEq E] in
@[simp] theorem fractionalExtension_apply_fixed (x : E → ℝ)
    (z : {e // IsFractional x e} → ℝ) {e : E} (he : ¬IsFractional x e) :
    fractionalExtension x z e = x e := by simp [fractionalExtension, he]

omit [Fintype E] [DecidableEq E] in
@[simp] theorem fractionalExtension_mean (x : E → ℝ) :
    fractionalExtension x (fractionalMean x) = x := by
  ext e
  by_cases he : IsFractional x e <;> simp [fractionalExtension, fractionalMean, he]

omit [Fintype E] [DecidableEq E] in
theorem fractionalExtension_injective (x : E → ℝ) :
    Function.Injective (fractionalExtension x) := by
  intro z w h
  ext e
  simpa using congrFun h e.val

omit [Fintype E] [DecidableEq E] in
theorem fractionalLinear_injective (x : E → ℝ) :
    Function.Injective (fractionalExtension x).linear := by
  intro z w h
  ext e
  have := congrFun h e.val
  simpa [fractionalExtension, e.property] using this

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem fractional_incident (G : LooplessGraph V E) (x : E → ℝ)
    (v : {v // FractionalVertex G x v}) (e : {e // IsFractional x e}) :
    (fractionalGraph G x).Incident v e ↔ G.Incident v.val e.val := by
  simp only [LooplessGraph.Incident, fractionalGraph, Subtype.ext_iff]

omit [Fintype V] [DecidableEq V] in
theorem fixed_or_zero (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {e : E} (he : ¬IsFractional x e) : x e = 0 ∨ x e = 1 := by
  have h := G.coordinate_mem_Icc hx e
  dsimp [IsFractional] at he
  by_cases hz : x e = 0
  · exact Or.inl hz
  · exact Or.inr (le_antisymm h.2 (not_lt.mp (fun hh => he ⟨lt_of_le_of_ne h.1 (Ne.symm hz), hh⟩)))

omit [Fintype V] [DecidableEq V] in
theorem incident_forced_zero (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {v : V} {e₀ e : E} (h₀ : x e₀ = 1) (hv₀ : G.Incident v e₀)
    (hv : G.Incident v e) (hne : e ≠ e₀) : x e = 0 := by
  apply G.forced_coordinate_zero hx e₀ h₀ hne
  intro hr
  rcases hv with h | h
  · exact hr.1 (h ▸ hv₀)
  · exact hr.2 (h ▸ hv₀)

omit [Fintype V] [DecidableEq V] in
theorem fractional_no_forced (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {v : V} (hv : FractionalVertex G x v) {e : E} (he : x e = 1) : ¬G.Incident v e := by
  intro hi
  obtain ⟨f, hf, hif⟩ := hv
  have hne : f ≠ e := by intro h; subst f; exact (ne_of_lt hf.2) he
  have hz := incident_forced_zero G hx he hi hif hne
  exact (ne_of_gt hf.1) hz

omit [Fintype V] in
theorem positive_incident (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) (v : V) :
    ∃ e, G.Incident v e ∧ 0 < x e := by
  by_contra! hn
  have hc := G.polytope_subset_constraintPolytope hx
  have hz : G.degree x v = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    by_cases hi : G.Incident v e
    · simp [hi, le_antisymm (hn e hi) (hc.1 e)]
    · simp [hi]
  rw [hc.2.1 v] at hz
  norm_num at hz

omit [Fintype V] in
theorem fixed_at_vertex (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {v : V} (hv : ¬FractionalVertex G x v) : ∃! e, x e = 1 ∧ G.Incident v e := by
  obtain ⟨e, hi, he⟩ := positive_incident G hx v
  have hnot : ¬IsFractional x e := fun h => hv ⟨e, h, hi⟩
  have hone : x e = 1 := (fixed_or_zero G hx hnot).resolve_left (ne_of_gt he)
  refine ⟨e, ⟨hone, hi⟩, ?_⟩
  intro f hf
  by_contra hn
  have hz := incident_forced_zero G hx hone hi hf.2 hn
  linarith [hf.1]

def fractionalAdd (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    (M : (fractionalGraph G x).Matching) : G.Matching := by
  classical
  let N := M.val.map (Function.Embedding.subtype (IsFractional x)) ∪
    Finset.univ.filter (fun e => x e = 1)
  have hmem (e : E) : e ∈ N ↔
      (∃ he : IsFractional x e, (⟨e,he⟩ : {e // IsFractional x e}) ∈ M.val) ∨ x e = 1 := by
    simp only [N, Finset.mem_union, Finset.mem_map, Function.Embedding.coe_subtype,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨f, hf, rfl⟩ | h)
      · exact Or.inl ⟨f.property, hf⟩
      · exact Or.inr h
    · rintro (⟨he, hm⟩ | h)
      · exact Or.inl ⟨⟨e,he⟩, hm, rfl⟩
      · exact Or.inr h
  refine ⟨N, ?_⟩
  intro v
  by_cases hv : FractionalVertex G x v
  · obtain ⟨e, ⟨he, hi⟩, hu⟩ := M.property ⟨v,hv⟩
    refine ⟨e.val, ⟨(hmem e.val).mpr (Or.inl ⟨e.property,he⟩),
      (fractional_incident G x _ _).mp hi⟩, ?_⟩
    intro f hf
    rcases (hmem f).mp hf.1 with ⟨hfrac, hm⟩ | hone
    · exact congrArg Subtype.val (hu ⟨f,hfrac⟩ ⟨hm, (fractional_incident G x _ _).mpr hf.2⟩)
    · exact (fractional_no_forced G hx hv hone hf.2).elim
  · obtain ⟨e, he, hu⟩ := fixed_at_vertex G hx hv
    refine ⟨e, ⟨(hmem e).mpr (Or.inr he.1), he.2⟩, ?_⟩
    intro f hf
    rcases (hmem f).mp hf.1 with ⟨hfrac, _⟩ | hone
    · exact (hv ⟨f,hfrac,hf.2⟩).elim
    · exact hu f ⟨hone,hf.2⟩

omit [Fintype V] in
theorem mem_fractionalAdd (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    (M : (fractionalGraph G x).Matching) (e : E) :
    e ∈ (fractionalAdd G hx M).val ↔
      (∃ he : IsFractional x e, (⟨e,he⟩ : {e // IsFractional x e}) ∈ M.val) ∨ x e = 1 := by
  classical
  simp only [fractionalAdd, Finset.mem_union, Finset.mem_map, Function.Embedding.coe_subtype,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨f,hf,rfl⟩ | h)
    · exact Or.inl ⟨f.property,hf⟩
    · exact Or.inr h
  · rintro (⟨he,hm⟩ | h)
    · exact Or.inl ⟨⟨e,he⟩,hm,rfl⟩
    · exact Or.inr h

omit [Fintype V] in
@[simp] theorem mem_fractionalAdd_fractional (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (M : (fractionalGraph G x).Matching) (e : {e // IsFractional x e}) :
    e.val ∈ (fractionalAdd G hx M).val ↔ e ∈ M.val := by
  rw [mem_fractionalAdd]
  simp only [exists_prop, Subtype.coe_eta]
  constructor
  · rintro (⟨_, hm⟩ | h)
    · exact hm
    · exact ((ne_of_lt e.property.2) h).elim
  · intro h
    exact Or.inl ⟨e.property,h⟩

omit [Fintype V] in
theorem fractionalAdd_injective (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    Function.Injective (fractionalAdd G hx) := by
  intro M N h
  apply Subtype.ext
  ext e
  rw [← mem_fractionalAdd_fractional G hx M e, ← mem_fractionalAdd_fractional G hx N e, h]

def FixedMatching (G : LooplessGraph V E) (x : E → ℝ) (M : G.Matching) : Prop :=
  ∀ e, ¬IsFractional x e → (e ∈ M.val ↔ x e = 1)

def fractionalRemove (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    (M : G.Matching) (hM : FixedMatching G x M) : (fractionalGraph G x).Matching := by
  classical
  refine ⟨Finset.univ.filter (fun e => e.val ∈ M.val), ?_⟩
  intro v
  obtain ⟨e, ⟨he, hi⟩, hu⟩ := M.property v.val
  have hefrac : IsFractional x e := by
    by_contra hn
    exact fractional_no_forced G hx v.property ((hM e hn).mp he) hi
  refine ⟨⟨e,hefrac⟩, ⟨by simpa using he, (fractional_incident G x _ _).mpr hi⟩, ?_⟩
  intro f hf
  apply Subtype.ext
  exact hu f.val ⟨by simpa using hf.1, (fractional_incident G x _ _).mp hf.2⟩

omit [Fintype V] in
theorem fractionalAdd_range (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    (M : G.Matching) : M ∈ Set.range (fractionalAdd G hx) ↔ FixedMatching G x M := by
  constructor
  · rintro ⟨N,rfl⟩ e he
    rw [mem_fractionalAdd]
    simp [he]
  · intro hM
    refine ⟨fractionalRemove G hx M hM, ?_⟩
    apply Subtype.ext
    ext e
    by_cases he : IsFractional x e
    · rw [← (show (⟨e,he⟩ : {e // IsFractional x e}).val = e from rfl)]
      rw [mem_fractionalAdd_fractional]
      simp [fractionalRemove]
    · rw [mem_fractionalAdd]
      simp [he, hM e he]

omit [Fintype V] [DecidableEq V] in
theorem law_zero_of_mean_zero (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) {e : E} (he : G.mean p e = 0)
    (M : G.Matching) (hM : e ∈ M.val) : p M = 0 := by
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun N (_ : N ∈ Finset.univ) =>
    mul_nonneg (hp.1 N) (G.indicator_nonneg N e))).mp he M (by simp)
  simpa [LooplessGraph.indicator, hM] using hz

omit [Fintype V] [DecidableEq V] in
theorem fractional_law_support (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {z : {e // IsFractional x e} → ℝ} {p : G.Matching → ℝ}
    (hp : p ∈ G.feasibleLaws (fractionalExtension x z)) {M : G.Matching} (hM : p M ≠ 0) :
    FixedMatching G x M := by
  intro e he
  have hm : G.mean p e = x e := by rw [hp.2, fractionalExtension_apply_fixed x z he]
  rcases fixed_or_zero G hx he with hz | ho
  · constructor
    · intro h
      exact (hM (law_zero_of_mean_zero G hp.1 (hm.trans hz) M h)).elim
    · intro h
      linarith
  · refine ⟨fun _ => ho, fun _ => ?_⟩
    by_contra hn
    exact hM (G.law_support_of_mean_one hp.1 (hm.trans ho) M hn)

theorem fiberMass_injective_apply {A : Type uA} {B : Type uB} [Fintype A] [DecidableEq B]
    (p : A → ℝ) (f : A → B) (hf : Function.Injective f) (a : A) :
    fiberMass p f (f a) = p a := by
  classical
  simp [fiberMass, hf.eq_iff]

theorem fiberMass_outside {A : Type uA} {B : Type uB} [Fintype A] [DecidableEq B]
    (p : A → ℝ) (f : A → B) (b : B) (hb : b ∉ Set.range f) : fiberMass p f b = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  exact ite_eq_right (fun h => hb ⟨a,h⟩)

theorem fiberMass_pullback {A : Type uA} {B : Type uB} [Fintype A] [DecidableEq B]
    (p : B → ℝ) (f : A → B) (hf : Function.Injective f)
    (hp : ∀ b, b ∉ Set.range f → p b = 0) :
    fiberMass (fun a => p (f a)) f = p := by
  ext b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a,rfl⟩ := hb
    exact fiberMass_injective_apply _ _ hf a
  · rw [fiberMass_outside _ _ _ hb, hp b hb]

theorem simplex_of_fiberMass {A : Type uA} {B : Type uB} [Fintype A] [Fintype B] [DecidableEq B]
    (p : A → ℝ) (f : A → B) (hf : Function.Injective f)
    (hp : fiberMass p f ∈ probabilitySimplex B) : p ∈ probabilitySimplex A := by
  refine ⟨fun a => ?_, ?_⟩
  · simpa only [fiberMass_injective_apply p f hf] using hp.1 (f a)
  · rw [← fiberMass_sum p f]
    exact hp.2

omit [Fintype V] in
theorem fractionalAdd_indicator (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    (M : (fractionalGraph G x).Matching) :
    G.indicator (fractionalAdd G hx M) = fractionalExtension x ((fractionalGraph G x).indicator M) := by
  ext e
  by_cases he : IsFractional x e
  · rw [← (show (⟨e,he⟩ : {e // IsFractional x e}).val = e from rfl),
      fractionalExtension_apply_fractional]
    simp only [LooplessGraph.indicator, mem_fractionalAdd_fractional G hx M ⟨e,he⟩]
  · rw [fractionalExtension_apply_fixed x _ he]
    simp only [LooplessGraph.indicator, mem_fractionalAdd]
    rcases fixed_or_zero G hx he with h | h <;> simp [he,h]

omit [Fintype V] in
theorem fractional_mean_push (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {q : (fractionalGraph G x).Matching → ℝ} (hq : q ∈ probabilitySimplex (fractionalGraph G x).Matching) :
    G.mean (fiberMass q (fractionalAdd G hx)) =
      fractionalExtension x ((fractionalGraph G x).mean q) := by
  ext e
  rw [LooplessGraph.mean, fiberMass_expect]
  simp_rw [fractionalAdd_indicator G hx]
  by_cases he : IsFractional x e
  · simp only [fractionalExtension, he, ↓reduceDIte, AffineMap.coe_mk]
    rfl
  · simp only [fractionalExtension_apply_fixed x _ he]
    rw [← Finset.sum_mul, hq.2, one_mul]

omit [Fintype V] in
theorem fractional_pull_feasible (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {z : {e // IsFractional x e} → ℝ} {p : G.Matching → ℝ}
    (hp : p ∈ G.feasibleLaws (fractionalExtension x z)) :
    p = fiberMass (fun N => p (fractionalAdd G hx N)) (fractionalAdd G hx) ∧
    (fun N => p (fractionalAdd G hx N)) ∈ (fractionalGraph G x).feasibleLaws z := by
  have hinj := fractionalAdd_injective G hx
  have hpe : fiberMass (fun N => p (fractionalAdd G hx N)) (fractionalAdd G hx) = p := by
    apply fiberMass_pullback _ _ hinj
    intro M hM
    by_contra hn
    exact hM ((fractionalAdd_range G hx M).mpr (fractional_law_support G hx hp hn))
  have hsimplex : (fun N => p (fractionalAdd G hx N)) ∈ probabilitySimplex (fractionalGraph G x).Matching :=
    simplex_of_fiberMass _ _ hinj (by rw [hpe]; exact hp.1)
  refine ⟨hpe.symm, hsimplex, fractionalExtension_injective x ?_⟩
  rw [← fractional_mean_push G hx hsimplex, hpe, hp.2]

omit [Fintype V] in
theorem fractional_feasible_iff (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    (z : {e // IsFractional x e} → ℝ) (q : (fractionalGraph G x).Matching → ℝ) :
    q ∈ (fractionalGraph G x).feasibleLaws z ↔
      fiberMass q (fractionalAdd G hx) ∈ G.feasibleLaws (fractionalExtension x z) := by
  constructor
  · intro hq
    exact ⟨fiberMass_mem_simplex hq.1 _, (fractional_mean_push G hx hq.1).trans (congrArg _ hq.2)⟩
  · intro hp
    have hq := (fractional_pull_feasible G hx hp).2
    simpa only [fiberMass_injective_apply q _ (fractionalAdd_injective G hx)] using hq

omit [Fintype V] in
theorem fractional_image_eq (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    fractionalExtension x '' (fractionalGraph G x).polytope = fixedFace G x := by
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨q,hq⟩ := ((fractionalGraph G x).mem_polytope_iff z).mp hz
    exact ⟨(G.mem_polytope_iff _).mpr ⟨_, (fractional_feasible_iff G hx z q).mp hq⟩,
      fun e he => fractionalExtension_apply_fixed x z he⟩
  · intro hy
    let z : {e // IsFractional x e} → ℝ := fun e => y e.val
    have hext : fractionalExtension x z = y := by
      ext e
      by_cases he : IsFractional x e
      · simp [fractionalExtension,he,z]
      · simp [fractionalExtension,he,hy.2 e he]
    obtain ⟨p,hp⟩ := (G.mem_polytope_iff _).mp hy.1
    have hp' : p ∈ G.feasibleLaws (fractionalExtension x z) := hext ▸ hp
    exact ⟨z, ((fractionalGraph G x).mem_polytope_iff z).mpr
      ⟨_,(fractional_pull_feasible G hx hp').2⟩, hext⟩

omit [Fintype V] in
theorem fractionalMean_mem (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    fractionalMean x ∈ (fractionalGraph G x).polytope := by
  have h : x ∈ fixedFace G x := ⟨hx,fun _ _ => rfl⟩
  rw [← fractional_image_eq G hx] at h
  obtain ⟨z,hz,he⟩ := h
  have : z = fractionalMean x := fractionalExtension_injective x (he.trans (fractionalExtension_mean x).symm)
  exact this ▸ hz

omit [Fintype V] [DecidableEq V] in
theorem fixedFace_extreme (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    IsExtreme ℝ G.polytope (fixedFace G x) := by
  refine ⟨fun _ h => h.1, ?_⟩
  intro y hy z hz w hw hseg
  obtain ⟨a,b,ha,hb,hab,rfl⟩ := hseg
  refine ⟨hy, ?_⟩
  intro e he
  have heq := hw.2 e he
  change a * y e + b * z e = x e at heq
  have hyb := G.coordinate_mem_Icc hy e
  have hzb := G.coordinate_mem_Icc hz e
  rcases hyb with ⟨hy0,hy1⟩
  rcases hzb with ⟨hz0,hz1⟩
  rcases fixed_or_zero G hx he with h | h
  · rw [h] at heq ⊢
    have := mul_nonneg hb.le hz0
    nlinarith
  · rw [h] at heq ⊢
    apply le_antisymm hy1
    by_contra! hn
    have hpos := mul_pos ha (sub_pos.mpr hn)
    have hnonneg := mul_nonneg hb.le (sub_nonneg.mpr hz1)
    nlinarith

section AffineFaces
variable {A : Type uA} {B : Type uB} [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]

theorem extreme_affine_image (f : A →ᵃ[ℝ] B) (hf : Function.Injective f)
    {P Q : Set A} (h : IsExtreme ℝ P Q) : IsExtreme ℝ (f '' P) (f '' Q) := by
  refine ⟨Set.image_mono h.subset, ?_⟩
  rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩ hseg
  rw [← image_openSegment ℝ f] at hseg
  obtain ⟨w',hw',he⟩ := hseg
  have hww : w' = w := hf he
  exact ⟨u, h.left_mem_of_mem_openSegment hu hv hw (hww ▸ hw'), rfl⟩

theorem extreme_affine_preimage (f : A →ᵃ[ℝ] B) {P : Set A} {Q R : Set B}
    (hPQ : f '' P ⊆ Q) (hQR : IsExtreme ℝ Q R) :
    IsExtreme ℝ P (P ∩ f ⁻¹' R) := by
  refine ⟨Set.inter_subset_left, ?_⟩
  intro u hu v hv w hw hseg
  refine ⟨hu, hQR.left_mem_of_mem_openSegment (hPQ ⟨u,hu,rfl⟩)
    (hPQ ⟨v,hv,rfl⟩) hw.2 ?_⟩
  rw [← image_openSegment ℝ f]
  exact ⟨w,hseg,rfl⟩
end AffineFaces

section FaceMaps
variable {W : Type uW} {D : Type uD} [Fintype W] [Fintype D] [DecidableEq W] [DecidableEq D]

theorem minimalFace_map (G : LooplessGraph V E) (H : LooplessGraph W D)
    (f : (D → ℝ) →ᵃ[ℝ] (E → ℝ)) (hf : Function.Injective f)
    (hP : IsExtreme ℝ G.polytope (f '' H.polytope))
    {z : D → ℝ} (hz : z ∈ H.polytope) :
    f '' minimalFace H z = minimalFace G (f z) := by
  have hfg : f z ∈ G.polytope := hP.subset ⟨z,hz,rfl⟩
  have ⟨hzz, _, hHz, hminH⟩ := minimalFace_spec H hz
  have ⟨hfz, _, hGz, hminG⟩ := minimalFace_spec G hfg
  apply Set.Subset.antisymm
  · have hp := extreme_affine_preimage f hP.subset hGz
    have hsub := hminH _ hp ⟨hz,hfz⟩
    rintro _ ⟨u,hu,rfl⟩
    exact (hsub hu).2
  · exact hminG _ (hP.trans (extreme_affine_image f hf hHz)) ⟨z,hzz,rfl⟩

theorem faceDimension_map (G : LooplessGraph V E) (H : LooplessGraph W D)
    (f : (D → ℝ) →ᵃ[ℝ] (E → ℝ)) (hf : Function.Injective f)
    (hP : IsExtreme ℝ G.polytope (f '' H.polytope))
    {z : D → ℝ} (hz : z ∈ H.polytope) :
    faceDimension H z = faceDimension G (f z) := by
  rw [faceDimension, faceDimension, ← minimalFace_map G H f hf hP hz,
    ← AffineSubspace.map_span, AffineSubspace.map_direction]
  exact (Submodule.equivMapOfInjective _ (f.linear_injective_iff.mpr hf) _).finrank_eq
end FaceMaps

theorem fractional_minimalFace (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    fractionalExtension x '' minimalFace (fractionalGraph G x) (fractionalMean x) = minimalFace G x := by
  have hextreme : IsExtreme ℝ G.polytope (fractionalExtension x '' (fractionalGraph G x).polytope) :=
    (fractional_image_eq G hx).symm ▸ fixedFace_extreme G hx
  simpa only [fractionalExtension_mean] using minimalFace_map G (fractionalGraph G x)
    (fractionalExtension x) (fractionalExtension_injective x) hextreme (fractionalMean_mem G hx)

theorem fractional_dimension (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    faceDimension (fractionalGraph G x) (fractionalMean x) = faceDimension G x := by
  have hextreme : IsExtreme ℝ G.polytope (fractionalExtension x '' (fractionalGraph G x).polytope) :=
    (fractional_image_eq G hx).symm ▸ fixedFace_extreme G hx
  simpa only [fractionalExtension_mean] using faceDimension_map G (fractionalGraph G x)
    (fractionalExtension x) (fractionalExtension_injective x) hextreme (fractionalMean_mem G hx)

omit [Fintype V] [DecidableEq V] in
theorem fractional_entropy_terms (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    entropy (fractionalMean x) = entropy x ∧
      complementEntropy (fractionalMean x) = complementEntropy x := by
  constructor
  · unfold entropy fractionalMean
    apply sum_subtype_supported (IsFractional x) (fun e => Real.negMulLog (x e))
    intro e he
    rcases fixed_or_zero G hx he with h | h <;> simp [h]
  · unfold complementEntropy
    unfold entropy fractionalMean
    apply sum_subtype_supported (IsFractional x) (fun e => Real.negMulLog (1-x e))
    intro e he
    rcases fixed_or_zero G hx he with h | h <;> simp [h]

omit [Fintype V] in
theorem fractional_maxEntropy (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {z : {e // IsFractional x e} → ℝ} (hz : z ∈ (fractionalGraph G x).polytope) :
    maxMatchingEntropy G (fractionalExtension x z) = maxMatchingEntropy (fractionalGraph G x) z := by
  obtain ⟨q,hq,hqopt⟩ := maxMatchingEntropy_attained (fractionalGraph G x) hz
  have hq' := (fractional_feasible_iff G hx z q).mp hq
  have hz' := (G.mem_polytope_iff _).mpr ⟨_,hq'⟩
  obtain ⟨p,hp,hpopt⟩ := maxMatchingEntropy_attained G hz'
  have ⟨hpe,hp'⟩ := fractional_pull_feasible G hx hp
  apply le_antisymm
  · rw [← hpopt, hpe, entropy_fiberMass_injective _ _ (fractionalAdd_injective G hx)]
    exact entropy_le_maxMatchingEntropy _ hp'
  · rw [← hqopt, ← entropy_fiberMass_injective q _ (fractionalAdd_injective G hx)]
    exact entropy_le_maxMatchingEntropy _ hq'

theorem fractional_laws {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    ∃ lift : (fractionalGraph G x).Matching → G.Matching, Function.Injective lift ∧
      (∀ z q, q ∈ (fractionalGraph G x).feasibleLaws z ↔
        fiberMass q lift ∈ G.feasibleLaws (fractionalExtension x z)) ∧
      (∀ z p, p ∈ G.feasibleLaws (fractionalExtension x z) →
        p = fiberMass (fun N => p (lift N)) lift ∧
        (fun N => p (lift N)) ∈ (fractionalGraph G x).feasibleLaws z) ∧
      (∀ z ∈ (fractionalGraph G x).polytope,
        maxMatchingEntropy G (fractionalExtension x z) = maxMatchingEntropy (fractionalGraph G x) z) ∧
      entropy (fractionalMean x) = entropy x ∧
      complementEntropy (fractionalMean x) = complementEntropy x := by
  exact ⟨fractionalAdd G hx, fractionalAdd_injective G hx, fractional_feasible_iff G hx,
    fun _ _ hp => fractional_pull_feasible G hx hp, fun _ hz => fractional_maxEntropy G hx hz,
    fractional_entropy_terms G hx⟩

theorem fractional_reduction (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    IsExtreme ℝ G.polytope (fixedFace G x) ∧
    Function.Injective (fractionalExtension x) ∧
    fractionalExtension x '' (fractionalGraph G x).polytope = fixedFace G x ∧
    fractionalExtension x '' minimalFace (fractionalGraph G x) (fractionalMean x) = minimalFace G x ∧
    faceDimension (fractionalGraph G x) (fractionalMean x) = faceDimension G x ∧
    ∃ m_f : ℕ, Fintype.card {v // FractionalVertex G x v} = 2 * m_f ∧
      (∑ e : {e // IsFractional x e}, x e.val) = (m_f : ℝ) ∧
      (0 < m_f → Fintype.card {e // IsFractional x e} + 2 ≤ faceDimension G x + 3 * m_f) ∧
      (m_f = 0 → ∃ M : G.Matching, G.indicator M = x ∧ faceDimension G x = 0) := by
  have hz := fractionalMean_mem G hx
  have hd := fractional_dimension G hx
  refine ⟨fixedFace_extreme G hx, fractionalExtension_injective x, fractional_image_eq G hx,
    fractional_minimalFace G hx, hd, ?_⟩
  obtain ⟨m,hm⟩ := even_of_mem (fractionalGraph G x) hz
  have hm' : Fintype.card {v // FractionalVertex G x v} = 2 * m := by omega
  refine ⟨m,hm',(fractionalGraph G x).marginal_sum hm' hz,?_,?_⟩
  · intro hm0
    have hr := minimalFace_rank (fractionalGraph G x) m hm0 hm' hz
    have hc : Fintype.card {e : {e // IsFractional x e} // 0 < fractionalMean x e} =
        Fintype.card {e // IsFractional x e} :=
      Fintype.card_congr (Equiv.subtypeUnivEquiv (fun e => e.property.1))
    rwa [hc,hd] at hr
  · intro hm0
    have hvzero : Fintype.card {v // FractionalVertex G x v} = 0 := by omega
    have : IsEmpty {v // FractionalVertex G x v} := Fintype.card_eq_zero_iff.mp hvzero
    have : IsEmpty {e // IsFractional x e} := ⟨fun e => isEmptyElim ((fractionalGraph G x).left e)⟩
    obtain ⟨M⟩ := matching_nonempty_of_mem (fractionalGraph G x) hz
    refine ⟨fractionalAdd G hx M, ?_, ?_⟩
    · rw [fractionalAdd_indicator G hx]
      have hM : (fractionalGraph G x).indicator M = fractionalMean x := Subsingleton.elim _ _
      rw [hM, fractionalExtension_mean]
    · rw [← hd, faceDimension]
      have hle := (affineSpan ℝ (minimalFace (fractionalGraph G x) (fractionalMean x))).direction.finrank_le
      have hzdim : Module.finrank ℝ ({e // IsFractional x e} → ℝ) = 0 := by simp
      rw [hzdim] at hle
      exact Nat.eq_zero_of_le_zero hle

end MatchingEntropyBounds.Refined

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds.Refined

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def underlyingSimple (G : LooplessGraph V E) : SimpleGraph V where
  Adj v w := ∃ e, (G.left e = v ∧ G.right e = w) ∨ (G.left e = w ∧ G.right e = v)
  symm := ⟨by
    rintro v w ⟨e, h | h⟩
    · exact ⟨e, Or.inr h⟩
    · exact ⟨e, Or.inl h⟩⟩
  loopless := ⟨by
    rintro v ⟨e, h | h⟩ <;> exact G.loopless e (h.1.trans h.2.symm)⟩

abbrev Component (G : LooplessGraph V E) := (underlyingSimple G).ConnectedComponent
noncomputable instance componentFintype (G : LooplessGraph V E) : Fintype (Component G) := Fintype.ofFinite _
noncomputable instance componentDecidableEq (G : LooplessGraph V E) : DecidableEq (Component G) := Classical.decEq _

def componentOf (G : LooplessGraph V E) (v : V) : Component G :=
  (underlyingSimple G).connectedComponentMk v

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem component_edge_eq (G : LooplessGraph V E) (e : E) :
    componentOf G (G.left e) = componentOf G (G.right e) :=
  SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ⟨e, Or.inl ⟨rfl,rfl⟩⟩

def componentGraph (G : LooplessGraph V E) (c : Component G) :
    LooplessGraph {v // componentOf G v = c} {e // componentOf G (G.left e) = c} where
  left e := ⟨G.left e.val,e.property⟩
  right e := ⟨G.right e.val,(component_edge_eq G e.val).symm.trans e.property⟩
  loopless e h := G.loopless e.val (congrArg Subtype.val h)

def componentMean (G : LooplessGraph V E) (x : E → ℝ) (c : Component G) :
    {e // componentOf G (G.left e) = c} → ℝ := fun e => x e.val

def componentOrder (G : LooplessGraph V E) (c : Component G) : ℕ :=
  Fintype.card {v // componentOf G v = c} / 2

section ProductLaws
variable {I : Type uI} [Fintype I] [DecidableEq I] {A : I → Type uA}
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

def piLaw (q : ∀ i, A i → ℝ) (a : ∀ i, A i) : ℝ := ∏ i, q i (a i)

omit [∀ i, DecidableEq (A i)] in
theorem piLaw_simplex {q : ∀ i, A i → ℝ} (hq : ∀ i, q i ∈ probabilitySimplex (A i)) :
    piLaw q ∈ probabilitySimplex (∀ i, A i) := by
  refine ⟨fun a => Finset.prod_nonneg (fun i _ => (hq i).1 (a i)), ?_⟩
  change (∑ a : ∀ i, A i, ∏ i, q i (a i)) = 1
  rw [← Fintype.prod_sum]
  simp_rw [(hq _).2]
  simp

omit [∀ i, DecidableEq (A i)] in
theorem piLaw_expect {q : ∀ i, A i → ℝ} (hq : ∀ i, q i ∈ probabilitySimplex (A i))
    (k : I) (f : A k → ℝ) :
    (∑ a : ∀ i, A i, piLaw q a * f (a k)) = ∑ b, q k b * f b := by
  let r : ∀ i, A i → ℝ := Function.update q k (fun b => q k b * f b)
  have heq (a : ∀ i, A i) : (∏ i, r i (a i)) = piLaw q a * f (a k) := by
    rw [Fintype.prod_eq_mul_prod_compl k (fun i => r i (a i)),
      piLaw, Fintype.prod_eq_mul_prod_compl k (fun i => q i (a i))]
    have hr : r k (a k) = q k (a k) * f (a k) := by simp [r]
    rw [hr]
    have hprod : (∏ i ∈ ({k}ᶜ : Finset I), r i (a i)) = ∏ i ∈ ({k}ᶜ : Finset I), q i (a i) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hik : i ≠ k := by simpa using hi
      simp [r, hik]
    rw [hprod]
    ring
  rw [← show (∑ a : ∀ i, A i, ∏ i, r i (a i)) = _ from Finset.sum_congr rfl (fun a _ => heq a),
    ← Fintype.prod_sum, Fintype.prod_eq_mul_prod_compl k]
  have hr : (∑ b, r k b) = ∑ b, q k b * f b := by simp [r]
  rw [hr]
  have hprod : (∏ i ∈ ({k}ᶜ : Finset I), ∑ b, r i b) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hik : i ≠ k := by simpa using hi
    simpa [r, hik] using (hq i).2
  rw [hprod, mul_one]

theorem piLaw_marginal {q : ∀ i, A i → ℝ} (hq : ∀ i, q i ∈ probabilitySimplex (A i))
    (k : I) : fiberMass (piLaw q) (fun a => a k) = q k := by
  ext b
  have h := piLaw_expect hq k (fun x => if x=b then 1 else 0)
  simpa [fiberMass, mul_ite] using h

theorem piLaw_crossEntropy (p : (∀ i, A i) → ℝ) (q : ∀ i, A i → ℝ)
    (hsupp : ∀ a, p a ≠ 0 → ∀ i, q i (a i) ≠ 0) :
    -(∑ a, p a * Real.log (piLaw q a)) =
      ∑ i, -(∑ b, fiberMass p (fun a => a i) b * Real.log (q i b)) := by
  have heq (a : ∀ i, A i) : p a * Real.log (piLaw q a) = ∑ i, p a * Real.log (q i (a i)) := by
    by_cases ha : p a = 0
    · simp [ha]
    · rw [piLaw, Real.log_prod (fun i _ => hsupp a ha i), Finset.mul_sum]
  simp_rw [heq]
  rw [Finset.sum_comm, Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (fiberMass_expect p (fun a => a i) (fun b => Real.log (q i b))).symm

theorem entropy_piLaw {q : ∀ i, A i → ℝ} (hq : ∀ i, q i ∈ probabilitySimplex (A i)) :
    entropy (piLaw q) = ∑ i, entropy (q i) := by
  rw [entropy_eq, piLaw_crossEntropy]
  · simp_rw [piLaw_marginal hq, ← entropy_eq]
  · intro a ha i
    exact (Finset.prod_ne_zero_iff.mp ha) i (Finset.mem_univ i)

theorem entropy_le_marginal_sum {p : (∀ i, A i) → ℝ}
    (hp : p ∈ probabilitySimplex (∀ i, A i)) :
    entropy p ≤ ∑ i, entropy (fiberMass p (fun a => a i)) := by
  let q : ∀ i, A i → ℝ := fun i => fiberMass p (fun a => a i)
  have hq : ∀ i, q i ∈ probabilitySimplex (A i) := fun i => fiberMass_mem_simplex hp _
  have hs : ∀ a, p a ≠ 0 → ∀ i, q i (a i) ≠ 0 := by
    intro a ha i
    exact ne_of_gt ((lt_of_le_of_ne (hp.1 a) (Ne.symm ha)).trans_le (le_fiberMass_self hp.1 _ a))
  have h := entropy_le_crossEntropy (piLaw_simplex hq) hp (fun a ha => by
    by_contra hpa
    exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hs a hpa i)) ha)
  rw [piLaw_crossEntropy p q hs] at h
  simpa only [q, ← entropy_eq] using h
end ProductLaws

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem component_incident_iff (G : LooplessGraph V E) (c : Component G)
    (v : {v // componentOf G v = c}) (e : {e // componentOf G (G.left e) = c}) :
    (componentGraph G c).Incident v e ↔ G.Incident v.val e.val := by
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem component_eq_of_incident (G : LooplessGraph V E) {v : V} {e : E} (h : G.Incident v e) :
    componentOf G (G.left e) = componentOf G v := by
  rcases h with h | h
  · rw [h]
  · rw [component_edge_eq G e, h]

def componentRestrict (G : LooplessGraph V E) (c : Component G) (M : G.Matching) :
    (componentGraph G c).Matching := by
  classical
  refine ⟨M.val.subtype (fun e => componentOf G (G.left e) = c), ?_⟩
  intro v
  obtain ⟨e,he,hu⟩ := M.property v.val
  have hc : componentOf G (G.left e) = c := (component_eq_of_incident G he.2).trans v.property
  refine ⟨⟨e,hc⟩, ⟨by simpa using he.1,(component_incident_iff G c v _).mpr he.2⟩, ?_⟩
  intro f hf
  exact Subtype.ext (hu f.val ⟨by simpa using hf.1,(component_incident_iff G c v f).mp hf.2⟩)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
@[simp] theorem mem_componentRestrict (G : LooplessGraph V E) (c : Component G) (M : G.Matching)
    (e : {e // componentOf G (G.left e) = c}) :
    e ∈ (componentRestrict G c M).val ↔ e.val ∈ M.val := by
  simp [componentRestrict]

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem componentRestrict_indicator (G : LooplessGraph V E) (c : Component G) (M : G.Matching)
    (e : {e // componentOf G (G.left e) = c}) :
    (componentGraph G c).indicator (componentRestrict G c M) e = G.indicator M e.val := by
  simp [LooplessGraph.indicator]

def componentGlue (G : LooplessGraph V E) (M : ∀ c : Component G, (componentGraph G c).Matching) :
    G.Matching := by
  classical
  let N := Finset.univ.filter (fun e => (⟨e,rfl⟩ : {f // componentOf G (G.left f) = componentOf G (G.left e)}) ∈ (M (componentOf G (G.left e))).val)
  have hmem (c : Component G) (e : {e // componentOf G (G.left e) = c}) : e.val ∈ N ↔ e ∈ (M c).val := by
    obtain ⟨e,he⟩ := e
    subst c
    simp [N]
  refine ⟨N, ?_⟩
  intro v
  obtain ⟨e,he,hu⟩ := (M (componentOf G v)).property ⟨v,rfl⟩
  refine ⟨e.val,⟨(hmem _ e).mpr he.1,(component_incident_iff G _ _ e).mp he.2⟩,?_⟩
  intro f hf
  have hfc := component_eq_of_incident G hf.2
  exact congrArg Subtype.val (hu ⟨f,hfc⟩ ⟨(hmem _ _).mp hf.1,(component_incident_iff G _ _ _).mpr hf.2⟩)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_componentGlue (G : LooplessGraph V E)
    (M : ∀ c : Component G, (componentGraph G c).Matching) (c : Component G)
    (e : {e // componentOf G (G.left e) = c}) :
    e.val ∈ (componentGlue G M).val ↔ e ∈ (M c).val := by
  obtain ⟨e,he⟩ := e
  subst c
  simp [componentGlue]

def componentMatchingEquiv (G : LooplessGraph V E) :
    G.Matching ≃ (∀ c : Component G, (componentGraph G c).Matching) where
  toFun := fun M c => componentRestrict G c M
  invFun := componentGlue G
  left_inv M := by
    apply Subtype.ext
    ext e
    exact (mem_componentGlue G _ _ ⟨e,rfl⟩).trans (mem_componentRestrict G _ M ⟨e,rfl⟩)
  right_inv M := by
    funext c
    apply Subtype.ext
    ext e
    rw [mem_componentRestrict, mem_componentGlue]

omit [Fintype V] in
omit [DecidableEq V] in
theorem component_mean_marginal (G : LooplessGraph V E) (c : Component G) (p : G.Matching → ℝ) :
    (componentGraph G c).mean (fiberMass p (componentRestrict G c)) = componentMean G (G.mean p) c := by
  ext e
  rw [LooplessGraph.mean, fiberMass_expect]
  simp_rw [componentRestrict_indicator]
  rfl

omit [Fintype V] in
omit [DecidableEq V] in
theorem component_feasible (G : LooplessGraph V E) (c : Component G)
    {x : E → ℝ} {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) :
    fiberMass p (componentRestrict G c) ∈ (componentGraph G c).feasibleLaws (componentMean G x c) := by
  exact ⟨fiberMass_mem_simplex hp.1 _, by rw [component_mean_marginal, hp.2]⟩

section FiberComposition
variable {A : Type uA} {B : Type uB} {C : Type uC} [Fintype A] [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
omit [Fintype C] in
theorem fiberMass_comp (p : A → ℝ) (f : A → B) (g : B → C) :
    fiberMass (fiberMass p f) g = fiberMass p (g ∘ f) := by
  ext c
  have h := fiberMass_expect p f (fun b => if g b = c then 1 else 0)
  simpa [fiberMass, mul_ite] using h
end FiberComposition

omit [DecidableEq V] in
theorem component_joint_entropy_bound (G : LooplessGraph V E)
    {p : G.Matching → ℝ} (hp : p ∈ probabilitySimplex G.Matching) :
    entropy p ≤ ∑ c : Component G, entropy (fiberMass p (componentRestrict G c)) := by
  have h := entropy_le_marginal_sum (fiberMass_mem_simplex hp (componentMatchingEquiv G))
  rw [entropy_fiberMass_injective _ _ (componentMatchingEquiv G).injective] at h
  simpa only [fiberMass_comp, Function.comp_def, componentMatchingEquiv, Equiv.coe_fn_mk] using h

omit [DecidableEq V] in
theorem component_product_feasible (G : LooplessGraph V E) {x : E → ℝ}
    {q : ∀ c : Component G, (componentGraph G c).Matching → ℝ}
    (hq : ∀ c, q c ∈ (componentGraph G c).feasibleLaws (componentMean G x c)) :
    fiberMass (piLaw q) (componentMatchingEquiv G).symm ∈ G.feasibleLaws x := by
  refine ⟨fiberMass_mem_simplex (piLaw_simplex (fun c => (hq c).1)) _, ?_⟩
  ext e
  let c := componentOf G (G.left e)
  let f : {e // componentOf G (G.left e) = c} := ⟨e,rfl⟩
  rw [LooplessGraph.mean, fiberMass_expect]
  have hi (M : ∀ c : Component G, (componentGraph G c).Matching) :
      G.indicator ((componentMatchingEquiv G).symm M) e = (componentGraph G c).indicator (M c) f := by
    simp only [LooplessGraph.indicator]
    change (if f.val ∈ (componentGlue G M).val then (1:ℝ) else 0) = _
    simp only [mem_componentGlue]
  simp_rw [hi]
  rw [piLaw_expect (fun c => (hq c).1) c (fun M => (componentGraph G c).indicator M f)]
  exact congrFun (hq c).2 f

omit [DecidableEq V] in
theorem component_maxEntropy (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    maxMatchingEntropy G x = ∑ c : Component G, maxMatchingEntropy (componentGraph G c) (componentMean G x c) := by
  obtain ⟨p,hp,hopt⟩ := maxMatchingEntropy_attained G hx
  have hc (c : Component G) : componentMean G x c ∈ (componentGraph G c).polytope :=
    ((componentGraph G c).mem_polytope_iff _).mpr ⟨_,component_feasible G c hp⟩
  choose q hq hqo using fun c => maxMatchingEntropy_attained (componentGraph G c) (hc c)
  apply le_antisymm
  · rw [← hopt]
    exact (component_joint_entropy_bound G hp.1).trans (Finset.sum_le_sum (fun c _ =>
      entropy_le_maxMatchingEntropy _ (component_feasible G c hp)))
  · have hh := entropy_le_maxMatchingEntropy G (component_product_feasible G hq)
    rw [entropy_fiberMass_injective _ _ (componentMatchingEquiv G).symm.injective,
      entropy_piLaw (fun c => (hq c).1)] at hh
    simpa only [hqo] using hh

omit [DecidableEq V] [DecidableEq E] in
theorem component_entropy_terms (G : LooplessGraph V E) (x : E → ℝ) :
    entropy x = ∑ c : Component G, entropy (componentMean G x c) ∧
    complementEntropy x = ∑ c : Component G, complementEntropy (componentMean G x c) := by
  constructor
  · exact (Fintype.sum_fiberwise (fun e => componentOf G (G.left e)) (fun e => Real.negMulLog (x e))).symm
  · exact (Fintype.sum_fiberwise (fun e => componentOf G (G.left e)) (fun e => Real.negMulLog (1-x e))).symm

theorem component_additivity (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    (∀ c : Component G, 0 < componentOrder G c ∧
      Fintype.card {v // componentOf G v = c} = 2 * componentOrder G c ∧
      componentMean G x c ∈ (componentGraph G c).polytope) ∧
    maxMatchingEntropy G x = ∑ c : Component G, maxMatchingEntropy (componentGraph G c) (componentMean G x c) ∧
    entropy x = ∑ c : Component G, entropy (componentMean G x c) ∧
    complementEntropy x = ∑ c : Component G, complementEntropy (componentMean G x c) := by
  refine ⟨?_,component_maxEntropy G hx,component_entropy_terms G x⟩
  intro c
  obtain ⟨p,hp⟩ := (G.mem_polytope_iff x).mp hx
  have hr := (componentGraph G c).mean_mem_polytope (component_feasible G c hp).1
  rw [(component_feasible G c hp).2] at hr
  have hev := even_of_mem (componentGraph G c) hr
  obtain ⟨v,hv⟩ := c.exists_rep
  have hcpos : 0 < Fintype.card {v // componentOf G v = c} :=
    Fintype.card_pos_iff.mpr ⟨⟨v,hv⟩⟩
  refine ⟨?_,?_,hr⟩ <;> unfold componentOrder <;> obtain ⟨m,hm⟩ := hev <;> omega

theorem fractional_components (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    let R := fractionalGraph G x
    let z := fractionalMean x
    (∀ c : Component R, 0 < componentOrder R c ∧
      Fintype.card {v // componentOf R v = c} = 2 * componentOrder R c ∧
      componentMean R z c ∈ (componentGraph R c).polytope) ∧
    maxMatchingEntropy G x = ∑ c : Component R, maxMatchingEntropy (componentGraph R c) (componentMean R z c) ∧
    entropy x - (∑ c : Component R, (2 - 2 / (componentOrder R c : ℝ)) *
      complementEntropy (componentMean R z c)) ≤ maxMatchingEntropy G x ∧
    maxMatchingEntropy G x ≤ entropy x ∧
    (IsEmpty (Component R) → entropy x = 0 ∧ complementEntropy x = 0 ∧ maxMatchingEntropy G x = 0) := by
  dsimp only
  let R := fractionalGraph G x
  let z := fractionalMean x
  have hz := fractionalMean_mem G hx
  have ⟨ho,hH,hF,hB⟩ := component_additivity R hz
  have hHr : maxMatchingEntropy G x = maxMatchingEntropy R z := by
    simpa only [fractionalExtension_mean] using fractional_maxEntropy G hx hz
  have ⟨hFr,hBr⟩ := fractional_entropy_terms G hx
  refine ⟨ho,hHr.trans hH,?_,refined_upper G x hx,?_⟩
  · rw [hHr, hH, ← hFr, hF, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun c _ => refined_lower (componentGraph R c) (componentOrder R c)
      (ho c).1 (ho c).2.1 (componentMean R z c) (ho c).2.2)
  · intro hc
    have : IsEmpty (Component R) := hc
    constructor
    · rw [← hFr, hF]
      simp
    constructor
    · rw [← hBr, hB]
      simp
    · rw [hHr, hH]
      simp

end MatchingEntropyBounds.Refined

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds.Refined

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem empty_conventions (G : LooplessGraph V E) (hV : Fintype.card V = 0) :
    Fintype.card E = 0 ∧ Fintype.card G.Matching = 1 ∧ G.polytope = {0} ∧
    (∀ x ∈ G.polytope, entropy x = 0 ∧ complementEntropy x = 0 ∧ maxMatchingEntropy G x = 0) ∧
    (∀ β : E → ℝ, weightedPartition G β = 1 ∧ weightedObjective β 0 = 0) ∧
    (∀ k : ℕ, 1 ≤ k → (Real.exp (-2) * (k : ℝ))^0 = 1) := by
  have : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
  have : IsEmpty E := ⟨fun e => isEmptyElim (G.left e)⟩
  let M : G.Matching := ⟨∅,fun v => isEmptyElim v⟩
  have : Nonempty G.Matching := ⟨M⟩
  have : Subsingleton G.Matching := inferInstance
  have hc : Fintype.card G.Matching = 1 := by
    let : Unique G.Matching := ⟨⟨M⟩, fun _ => Subsingleton.elim _ _⟩
    exact Fintype.card_unique
  have hi : G.indicator M = 0 := Subsingleton.elim _ _
  have hp : G.polytope = {0} := by
    apply Set.Subset.antisymm
    · intro x _
      exact Set.mem_singleton_iff.mpr (Subsingleton.elim _ _)
    · rintro x rfl
      rw [← hi]
      exact subset_convexHull ℝ _ (Set.mem_range_self M)
  refine ⟨Fintype.card_eq_zero, hc, hp, ?_, ?_, fun _ _ => pow_zero _⟩
  · intro x hx
    have hF : entropy x = 0 := by simp [entropy]
    have hB : complementEntropy x = 0 := by simp [complementEntropy, entropy]
    refine ⟨hF,hB,le_antisymm ?_ (maxMatchingEntropy_nonneg G hx)⟩
    simpa [hF] using refined_upper G x hx
  · intro β
    constructor
    · simp [weightedPartition, hc]
    · simp [weightedObjective, entropy]

theorem no_matching_polytope {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) :
    IsEmpty G.Matching ↔ G.polytope = ∅ := by
  constructor
  · intro hm
    have : IsEmpty G.Matching := hm
    exact Set.eq_empty_iff_forall_notMem.mpr (fun x hx => by
      obtain ⟨M⟩ := matching_nonempty_of_mem G hx
      exact isEmptyElim M)
  · intro hp
    exact ⟨fun M => by
      have h := subset_convexHull ℝ (Set.range G.indicator) (Set.mem_range_self M)
      change G.indicator M ∈ G.polytope at h
      rw [hp] at h
      exact h⟩

theorem zero_selected_bound {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (m : ℕ) (hm : 0 < m) :
    (Real.exp (-2) * (0 : ℝ))^m = 0 ∧ (0 : ℝ) ≤ Fintype.card G.Matching := by
  simp [zero_pow (Nat.ne_of_gt hm)]

theorem zero_regular {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (hV : 0 < Fintype.card V)
    (hreg : ∀ v, (Finset.univ.filter (G.Incident v)).card = 0) :
    Fintype.card E = 0 ∧ IsEmpty G.Matching := by
  have he : IsEmpty E := by
    refine ⟨fun e => ?_⟩
    have hh := Finset.card_eq_zero.mp (hreg (G.left e))
    have hm : e ∈ Finset.univ.filter (G.Incident (G.left e)) := by
      simp [LooplessGraph.Incident]
    rw [hh] at hm
    exact Finset.notMem_empty e hm
  have : IsEmpty E := he
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hV
  exact ⟨Fintype.card_eq_zero, ⟨fun M => by obtain ⟨e,_,_⟩ := M.property v; exact isEmptyElim e⟩⟩

theorem one_selected_bound {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (M : G.Matching) :
    1 ≤ Fintype.card G.Matching := Fintype.card_pos_iff.mpr ⟨M⟩

theorem one_partition_exact {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (M : G.Matching)
    (hcover : M.val = Finset.univ) : Fintype.card G.Matching = 1 := by
  have hu : ∀ N : G.Matching, N = M := by
    intro N
    apply Subtype.ext
    apply Finset.Subset.antisymm
    · rw [hcover]
      exact Finset.subset_univ _
    · intro e he
      obtain ⟨f,hf,_⟩ := N.property (G.left e)
      have hfm : f ∈ M.val := hcover ▸ Finset.mem_univ f
      have hfe := (M.property (G.left e)).unique ⟨hfm,hf.2⟩ ⟨he,Or.inl rfl⟩
      exact hfe ▸ hf.1
  have : Subsingleton G.Matching := ⟨fun a b => (hu a).trans (hu b).symm⟩
  exact by
    let : Unique G.Matching := ⟨⟨M⟩, fun _ => Subsingleton.elim _ _⟩
    exact Fintype.card_unique

theorem pointwise_endpoints (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) {x : E → ℝ} (hx : x ∈ G.polytope) :
    entropy x - 2 * complementEntropy x ≤ maxMatchingEntropy G x ∧
      (m = 1 → maxMatchingEntropy G x = entropy x) := by
  have hl := refined_lower G m hm hV x hx
  change entropy x - (2 - 2 / (m : ℝ)) * complementEntropy x ≤ maxMatchingEntropy G x at hl
  have hB := B_nonneg G hx
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · have hpos := mul_nonneg (div_nonneg (by norm_num : (0:ℝ) ≤ 2) hmR.le) hB
    nlinarith
  · intro hh
    subst m
    norm_num at hl
    exact le_antisymm (refined_upper G x hx) hl

end MatchingEntropyBounds.Refined

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds.Refined

section TriangleExpansion
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def CubicColoring (G : LooplessGraph V E) (c : E → Fin 3) : Prop :=
  ∀ v i, ∃! e, G.Incident v e ∧ c e = i

def colorEdges (c : E → Fin 3) (i : Fin 3) : Finset E := Finset.univ.filter (fun e => c e = i)

def triangleTip (v : V) (i : Fin 3) : V ⊕ Fin 2 := ![Sum.inl v, Sum.inr 0, Sum.inr 1] i

def triangleCollapse (v : V) : V ⊕ Fin 2 → V := Sum.elim id (fun _ => v)

def reattach (v : V) (i : Fin 3) (w : V) : V ⊕ Fin 2 :=
  if w = v then triangleTip v i else Sum.inl w

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem collapse_reattach (v : V) (i : Fin 3) (w : V) :
    triangleCollapse v (reattach v i w) = w := by
  by_cases h : w = v
  · subst w
    fin_cases i <;> simp [reattach,triangleTip,triangleCollapse]
  · simp [reattach,h,triangleCollapse]

def triangleExpansion (G : LooplessGraph V E) (c : E → Fin 3) (v : V) :
    LooplessGraph (V ⊕ Fin 2) (E ⊕ Fin 3) where
  left := Sum.elim (fun e => reattach v (c e) (G.left e)) (fun i => triangleTip v (i + 1))
  right := Sum.elim (fun e => reattach v (c e) (G.right e)) (fun i => triangleTip v (i + 2))
  loopless := by
    intro e h
    rcases e with e | i
    · have hh := congrArg (triangleCollapse v) h
      exact G.loopless e ((collapse_reattach v (c e) (G.left e)).symm.trans
        (hh.trans (collapse_reattach v (c e) (G.right e))))
    · fin_cases i <;> simp [triangleTip] at h

def expandedColor (c : E → Fin 3) : E ⊕ Fin 3 → Fin 3 := Sum.elim c id

def triangleVertices (v : V) : Finset (V ⊕ Fin 2) := Finset.univ.image (triangleTip v)

def vertexColorEdge (G : LooplessGraph V E) (c : E → Fin 3) (hc : CubicColoring G c)
    (v : V) (i : Fin 3) : E := Classical.choose (hc v i)

def triangleExtension (G : LooplessGraph V E) (c : E → Fin 3) (hc : CubicColoring G c)
    (v : V) : (E → ℝ) →ₗ[ℝ] (E ⊕ Fin 3 → ℝ) where
  toFun x := Sum.elim x (fun i => x (vertexColorEdge G c hc v i))
  map_add' x y := by ext e; cases e <;> rfl
  map_smul' a x := by ext e; cases e <;> rfl

def IsSimpleLabelled (G : LooplessGraph V E) : Prop :=
  ∀ e f, ((G.left e = G.left f ∧ G.right e = G.right f) ∨
    (G.left e = G.right f ∧ G.right e = G.left f)) → e = f

end TriangleExpansion

def KleeV : ℕ → Type
  | 0 => Fin 2
  | n + 1 => KleeV n ⊕ Fin 2

def KleeE : ℕ → Type
  | 0 => Fin 3
  | n + 1 => KleeE n ⊕ Fin 3

noncomputable instance kleeVFintype (n : ℕ) : Fintype (KleeV n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (Fin 2))
  | succ n ih =>
    let : Fintype (KleeV n) := ih
    exact inferInstanceAs (Fintype (KleeV n ⊕ Fin 2))
noncomputable instance kleeEFintype (n : ℕ) : Fintype (KleeE n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (Fin 3))
  | succ n ih =>
    let : Fintype (KleeE n) := ih
    exact inferInstanceAs (Fintype (KleeE n ⊕ Fin 3))
noncomputable instance kleeVDecEq (n : ℕ) : DecidableEq (KleeV n) := Classical.decEq _
noncomputable instance kleeEDecEq (n : ℕ) : DecidableEq (KleeE n) := Classical.decEq _

def kleeRoot : (n : ℕ) → KleeV n
  | 0 => (0 : Fin 2)
  | n + 1 => Sum.inl (kleeRoot n)

def kleeColor : (n : ℕ) → KleeE n → Fin 3
  | 0 => id
  | n + 1 => expandedColor (kleeColor n)

def kleeGraph : (n : ℕ) → LooplessGraph (KleeV n) (KleeE n)
  | 0 => ⟨fun _ => (0 : Fin 2), fun _ => (1 : Fin 2), fun _ => by exact (by norm_num : (0 : Fin 2) ≠ 1)⟩
  | n + 1 => triangleExpansion (kleeGraph n) (kleeColor n) (kleeRoot n)

def kleeUniform (n : ℕ) : KleeE n → ℝ := fun _ => 1 / 3

def coloredVector {E : Type uE} (c : E → Fin 3) (i : Fin 3) : E → ℝ :=
  fun e => if c e = i then 1 else 0

def kleeTriangle (n : ℕ) : Set (KleeE n → ℝ) :=
  convexHull ℝ (Set.range (coloredVector (kleeColor n)))

def kleeLaw (n : ℕ) : (kleeGraph n).Matching → ℝ :=
  fun M => ∑ i : Fin 3, if M.val = colorEdges (kleeColor n) i then 1 / 3 else 0

section ExpansionSupport
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem triangleTip_injective (v : V) : Function.Injective (triangleTip v) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [triangleTip]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem reattach_eq_tip (v w : V) (i j : Fin 3) :
    reattach v i w = triangleTip v j ↔ w = v ∧ i = j := by
  by_cases h : w = v
  · simp [reattach,h,(triangleTip_injective v).eq_iff]
  · fin_cases j <;> simp [reattach,h,triangleTip]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem reattach_eq_inl (v w z : V) (hz : z ≠ v) (i : Fin 3) :
    reattach v i w = Sum.inl z ↔ w = z := by
  by_cases h : w = v
  · subst w
    fin_cases i <;> simp [reattach,triangleTip,hz.symm]
  · simp [reattach,h]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expanded_incident_old_tip (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (e : E) (j : Fin 3) :
    (triangleExpansion G c v).Incident (triangleTip v j) (Sum.inl e) ↔
      G.Incident v e ∧ c e = j := by
  simp only [LooplessGraph.Incident,triangleExpansion,Sum.elim_inl,reattach_eq_tip]
  tauto

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expanded_incident_old_inl (G : LooplessGraph V E) (c : E → Fin 3) (v w : V)
    (hw : w ≠ v) (e : E) :
    (triangleExpansion G c v).Incident (Sum.inl w) (Sum.inl e) ↔ G.Incident w e := by
  simp only [LooplessGraph.Incident,triangleExpansion,Sum.elim_inl,reattach_eq_inl v _ w hw]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expanded_incident_new_tip (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (i j : Fin 3) :
    (triangleExpansion G c v).Incident (triangleTip v j) (Sum.inr i) ↔ i ≠ j := by
  simp only [LooplessGraph.Incident,triangleExpansion,Sum.elim_inr,
    (triangleTip_injective v).eq_iff]
  fin_cases i <;> fin_cases j <;> decide

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expanded_incident_new_inl (G : LooplessGraph V E) (c : E → Fin 3) (v w : V)
    (hw : w ≠ v) (i : Fin 3) :
    ¬(triangleExpansion G c v).Incident (Sum.inl w) (Sum.inr i) := by
  fin_cases i <;> simp [LooplessGraph.Incident,triangleExpansion,triangleTip,hw.symm]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem vertexColorEdge_spec (G : LooplessGraph V E) (c : E → Fin 3) (hc : CubicColoring G c)
    (v : V) (i : Fin 3) :
    G.Incident v (vertexColorEdge G c hc v i) ∧ c (vertexColorEdge G c hc v i) = i :=
  (Classical.choose_spec (hc v i)).1

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem eq_vertexColorEdge (G : LooplessGraph V E) (c : E → Fin 3) (hc : CubicColoring G c)
    (v : V) {e : E} {i : Fin 3} (he : G.Incident v e) (hi : c e = i) :
    e = vertexColorEdge G c hc v i := (Classical.choose_spec (hc v i)).2 e ⟨he,hi⟩

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem colorEdges_matching (G : LooplessGraph V E) (c : E → Fin 3) (hc : CubicColoring G c)
    (i : Fin 3) : G.IsPerfectMatching (colorEdges c i) := by
  intro v
  obtain ⟨e, he, hu⟩ := hc v i
  refine ⟨e,⟨by simp [colorEdges,he.2],he.1⟩,?_⟩
  intro f hf
  exact hu f ⟨hf.2,by simpa [colorEdges] using hf.1⟩

omit [Fintype V] [DecidableEq V] in
def colorMatching (G : LooplessGraph V E) (c : E → Fin 3) (hc : CubicColoring G c)
    (i : Fin 3) : G.Matching := ⟨colorEdges c i,colorEdges_matching G c hc i⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem cubicColoring_expansion (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) : CubicColoring (triangleExpansion G c v) (expandedColor c) := by
  intro w i
  have htip (j : Fin 3) : ∃! e, (triangleExpansion G c v).Incident (triangleTip v j) e ∧ expandedColor c e = i := by
    by_cases hij : i = j
    · subst j
      refine ⟨Sum.inl (vertexColorEdge G c hc v i), ⟨?_,(vertexColorEdge_spec G c hc v i).2⟩, ?_⟩
      · exact (expanded_incident_old_tip G c v _ _).mpr (vertexColorEdge_spec G c hc v i)
      · intro e he
        rcases e with e | e
        · apply congrArg Sum.inl
          exact eq_vertexColorEdge G c hc v ((expanded_incident_old_tip G c v e i).mp he.1).1 he.2
        · exact ((expanded_incident_new_tip G c v e i).mp he.1 he.2).elim
    · refine ⟨Sum.inr i,⟨(expanded_incident_new_tip G c v i j).mpr hij,rfl⟩,?_⟩
      intro e he
      rcases e with e | e
      · have hej := ((expanded_incident_old_tip G c v e j).mp he.1).2
        exact (hij (he.2.symm.trans hej)).elim
      · exact congrArg Sum.inr he.2
  rcases w with w | w
  · by_cases hw : w = v
    · subst w
      exact htip 0
    · obtain ⟨e,he,hu⟩ := hc w i
      refine ⟨Sum.inl e,⟨(expanded_incident_old_inl G c v w hw e).mpr he.1,he.2⟩,?_⟩
      intro f hf
      rcases f with f | f
      · exact congrArg Sum.inl (hu f ⟨(expanded_incident_old_inl G c v w hw f).mp hf.1,hf.2⟩)
      · exact (expanded_incident_new_inl G c v w hw f hf.1).elim
  · fin_cases w
    · exact htip 1
    · exact htip 2

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem triangleVertices_eq (v : V) :
    triangleVertices v = {Sum.inl v, Sum.inr 0, Sum.inr 1} := by
  simp [triangleVertices,Fin.univ_succ,triangleTip]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem mem_triangleVertices_tip (v : V) (i : Fin 3) : triangleTip v i ∈ triangleVertices v :=
  Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem reattach_mem_triangle (v w : V) (i : Fin 3) :
    reattach v i w ∈ triangleVertices v ↔ w = v := by
  by_cases h : w = v
  · simp [reattach,h,mem_triangleVertices_tip]
  · simp [reattach,h,triangleVertices_eq]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expanded_crosses_old (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (e : E) :
    (triangleExpansion G c v).Crosses (triangleVertices v) (Sum.inl e) ↔ G.Incident v e := by
  have hl := G.loopless e
  simp only [LooplessGraph.Crosses,triangleExpansion,Sum.elim_inl,reattach_mem_triangle,
    LooplessGraph.Incident]
  constructor
  · tauto
  · rintro (h | h)
    · exact Or.inl ⟨h,fun hh => hl (h.trans hh.symm)⟩
    · exact Or.inr ⟨fun hh => hl (hh.trans h.symm),h⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expanded_crosses_new (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (i : Fin 3) :
    ¬(triangleExpansion G c v).Crosses (triangleVertices v) (Sum.inr i) := by
  simp [LooplessGraph.Crosses,triangleExpansion,mem_triangleVertices_tip]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem triangleVertices_odd (v : V) : Odd (triangleVertices v).card := by
  have hcard : (triangleVertices v).card = 3 := by
    rw [triangleVertices,Finset.card_image_of_injective _ (triangleTip_injective v)]
    simp
  rw [hcard]
  norm_num

omit [Fintype V] [DecidableEq E] in
theorem expanded_cutMass (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (y : E ⊕ Fin 3 → ℝ) :
    (triangleExpansion G c v).cutMass y (triangleVertices v) = G.degree (fun e => y (Sum.inl e)) v := by
  simp only [LooplessGraph.cutMass,LooplessGraph.cut,Finset.sum_filter,Fintype.sum_sum_type,
    expanded_crosses_old,expanded_crosses_new,ite_false,Finset.sum_const_zero,add_zero,
    LooplessGraph.degree]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
def incidentChoice (G : LooplessGraph V E) (M : G.Matching) (v : V) : E :=
  Classical.choose (M.property v)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem incidentChoice_spec (G : LooplessGraph V E) (M : G.Matching) (v : V) :
    incidentChoice G M v ∈ M.val ∧ G.Incident v (incidentChoice G M v) :=
  (Classical.choose_spec (M.property v)).1

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem eq_incidentChoice (G : LooplessGraph V E) (M : G.Matching) (v : V) {e : E}
    (he : e ∈ M.val) (hv : G.Incident v e) : e = incidentChoice G M v :=
  (Classical.choose_spec (M.property v)).2 e ⟨he,hv⟩

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
def expandEdges (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (M : G.Matching) :
    Finset (E ⊕ Fin 3) := M.val.disjSum {c (incidentChoice G M v)}

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expandEdges_matching (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (M : G.Matching) :
    (triangleExpansion G c v).IsPerfectMatching (expandEdges G c v M) := by
  let e := incidentChoice G M v
  have he := incidentChoice_spec G M v
  have htip (j : Fin 3) : ∃! f, f ∈ expandEdges G c v M ∧
      (triangleExpansion G c v).Incident (triangleTip v j) f := by
    by_cases hj : c e = j
    · refine ⟨Sum.inl e,⟨by simp [expandEdges,he.1,e],
        (expanded_incident_old_tip G c v e j).mpr ⟨he.2,hj⟩⟩,?_⟩
      intro f hf
      rcases f with f | f
      · have hfm : f ∈ M.val := by simpa [expandEdges] using hf.1
        exact congrArg Sum.inl (eq_incidentChoice G M v hfm
          ((expanded_incident_old_tip G c v f j).mp hf.2).1)
      · have hfcol : f = c e := by simpa [expandEdges,e] using hf.1
        exact ((expanded_incident_new_tip G c v f j).mp hf.2 (hfcol.trans hj)).elim
    · refine ⟨Sum.inr (c e),⟨by simp [expandEdges,e],
        (expanded_incident_new_tip G c v (c e) j).mpr hj⟩,?_⟩
      intro f hf
      rcases f with f | f
      · have hfm : f ∈ M.val := by simpa [expandEdges] using hf.1
        have hfv := (expanded_incident_old_tip G c v f j).mp hf.2
        have hfe : f = e := eq_incidentChoice G M v hfm hfv.1
        exact (hj (hfe ▸ hfv.2)).elim
      · exact congrArg Sum.inr (by simpa [expandEdges,e] using hf.1)
  intro w
  rcases w with w | w
  · by_cases hw : w = v
    · subst w
      exact htip 0
    · obtain ⟨f,hf,hu⟩ := M.property w
      refine ⟨Sum.inl f,⟨by simpa [expandEdges] using hf.1,
        (expanded_incident_old_inl G c v w hw f).mpr hf.2⟩,?_⟩
      intro g hg
      rcases g with g | g
      · exact congrArg Sum.inl (hu g ⟨by simpa [expandEdges] using hg.1,
          (expanded_incident_old_inl G c v w hw g).mp hg.2⟩)
      · exact (expanded_incident_new_inl G c v w hw g hg.2).elim
  · fin_cases w
    · exact htip 1
    · exact htip 2

omit [Fintype V] [Fintype E] [DecidableEq E] in
def expandMatching (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (M : G.Matching) :
    (triangleExpansion G c v).Matching := ⟨expandEdges G c v M,expandEdges_matching G c v M⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem expandMatching_injective (G : LooplessGraph V E) (c : E → Fin 3) (v : V) :
    Function.Injective (expandMatching G c v) := by
  intro M N h
  apply Subtype.ext
  ext e
  have hh := congrArg (fun K : (triangleExpansion G c v).Matching => Sum.inl e ∈ K.val) h
  simpa [expandMatching,expandEdges] using hh

omit [Fintype V] [Fintype E] in
theorem expandMatching_indicator (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) (M : G.Matching) :
    (triangleExpansion G c v).indicator (expandMatching G c v M) = triangleExtension G c hc v (G.indicator M) := by
  ext e
  rcases e with e | i
  · simp [LooplessGraph.indicator,expandMatching,expandEdges,triangleExtension]
  · have hh : c (incidentChoice G M v) = i ↔ vertexColorEdge G c hc v i ∈ M.val := by
      constructor
      · intro h
        rw [← eq_vertexColorEdge G c hc v (incidentChoice_spec G M v).2 h]
        exact (incidentChoice_spec G M v).1
      · intro h
        rw [← eq_incidentChoice G M v h (vertexColorEdge_spec G c hc v i).1]
        exact (vertexColorEdge_spec G c hc v i).2
    simp only [LooplessGraph.indicator,expandMatching,expandEdges,Finset.inr_mem_disjSum,
      Finset.mem_singleton,triangleExtension,LinearMap.coe_mk,AddHom.coe_mk,Sum.elim_inr]
    simp only [eq_comm (a := i) (b := c (incidentChoice G M v)),hh]

def CrossOnce (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching) : Prop :=
  ∃! e, Sum.inl e ∈ N.val ∧ G.Incident v e

omit [Fintype V] in
theorem cutMass_indicator_card (G : LooplessGraph V E) (M : G.Matching) (S : Finset V) :
    G.cutMass (G.indicator M) S = ((M.val.filter (G.Crosses S)).card : ℝ) := by
  simp only [LooplessGraph.cutMass,LooplessGraph.indicator,Finset.sum_boole]
  congr 2
  ext e
  simp [LooplessGraph.cut,and_comm]

omit [Fintype V] in
theorem crossOnce_of_cut_eq_one (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching)
    (hN : (triangleExpansion G c v).cutMass ((triangleExpansion G c v).indicator N) (triangleVertices v) = 1) :
    CrossOnce G c v N := by
  rw [cutMass_indicator_card] at hN
  have hn : (N.val.filter ((triangleExpansion G c v).Crosses (triangleVertices v))).card = 1 := by
    exact_mod_cast hN
  obtain ⟨f,hf⟩ := Finset.card_eq_one.mp hn
  have hfm : f ∈ N.val ∧ (triangleExpansion G c v).Crosses (triangleVertices v) f := by
    have hh : f ∈ N.val.filter ((triangleExpansion G c v).Crosses (triangleVertices v)) := by rw [hf]; simp
    exact Finset.mem_filter.mp hh
  rcases f with e | i
  · refine ⟨e,⟨hfm.1,(expanded_crosses_old G c v e).mp hfm.2⟩,?_⟩
    intro f hfg
    have hh : Sum.inl f ∈ N.val.filter ((triangleExpansion G c v).Crosses (triangleVertices v)) :=
      Finset.mem_filter.mpr ⟨hfg.1,(expanded_crosses_old G c v f).mpr hfg.2⟩
    rw [hf,Finset.mem_singleton] at hh
    exact Sum.inl.inj hh
  · exact (expanded_crosses_new G c v i hfm.2).elim

def contractEdges (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching) : Finset E :=
  Finset.univ.filter (fun e => Sum.inl e ∈ N.val)

omit [Fintype V] in
theorem contractEdges_matching (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching) (hN : CrossOnce G c v N) :
    G.IsPerfectMatching (contractEdges G c v N) := by
  intro w
  by_cases hw : w = v
  · subst w
    simpa only [CrossOnce,contractEdges,Finset.mem_filter,Finset.mem_univ,true_and] using hN
  · obtain ⟨f,hf,hu⟩ := N.property (Sum.inl w)
    rcases f with f | f
    · refine ⟨f,⟨by simpa [contractEdges] using hf.1,
        (expanded_incident_old_inl G c v w hw f).mp hf.2⟩,?_⟩
      intro g hg
      apply Sum.inl.inj
      exact hu (Sum.inl g) ⟨by simpa [contractEdges] using hg.1,
        (expanded_incident_old_inl G c v w hw g).mpr hg.2⟩
    · exact (expanded_incident_new_inl G c v w hw f hf.2).elim

def contractMatching (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching) (hN : CrossOnce G c v N) : G.Matching :=
  ⟨contractEdges G c v N,contractEdges_matching G c v N hN⟩

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem fin3_add_one_ne (i : Fin 3) : i + 1 ≠ i := by fin_cases i <;> decide

omit [Fintype V] in
theorem expand_contract (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching) (hN : CrossOnce G c v N) :
    expandMatching G c v (contractMatching G c v N hN) = N := by
  let M := contractMatching G c v N hN
  let e := incidentChoice G M v
  have he : Sum.inl e ∈ N.val ∧ G.Incident v e := by
    simpa [e,M,contractMatching,contractEdges] using incidentChoice_spec G M v
  have hcol : ∀ i : Fin 3, Sum.inr i ∈ N.val → i = c e := by
    intro i hi
    by_contra hn
    have hh := (N.property (triangleTip v (c e))).unique
      ⟨hi,(expanded_incident_new_tip G c v i (c e)).mpr hn⟩
      ⟨he.1,(expanded_incident_old_tip G c v e (c e)).mpr ⟨he.2,rfl⟩⟩
    cases hh
  have hmem : Sum.inr (c e) ∈ N.val := by
    obtain ⟨f,hf,_⟩ := N.property (triangleTip v (c e + 1))
    rcases f with f | i
    · have hfv := (expanded_incident_old_tip G c v f (c e + 1)).mp hf.2
      have hfe : f = e := hN.unique ⟨hf.1,hfv.1⟩ he
      have hh : c e = c e + 1 := hfe ▸ hfv.2
      exact (fin3_add_one_ne (c e) hh.symm).elim
    · exact hcol i hf.1 ▸ hf.1
  apply Subtype.ext
  ext f
  rcases f with f | i
  · simp [expandMatching,expandEdges,contractMatching,contractEdges]
  · simp only [expandMatching,expandEdges,Finset.inr_mem_disjSum,Finset.mem_singleton]
    change i = c e ↔ Sum.inr i ∈ N.val
    exact ⟨fun hi => hi ▸ hmem,hcol i⟩

omit [Fintype V] in
theorem range_expandMatching_of_crossOnce (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : (triangleExpansion G c v).Matching) (hN : CrossOnce G c v N) :
    N ∈ Set.range (expandMatching G c v) := ⟨contractMatching G c v N hN,expand_contract G c v N hN⟩

omit [Fintype V] in
theorem cutMass_mean (G : LooplessGraph V E) (p : G.Matching → ℝ) (S : Finset V) :
    G.cutMass (G.mean p) S = ∑ M, p M * G.cutMass (G.indicator M) S := by
  simp only [LooplessGraph.cutMass,LooplessGraph.mean,Finset.mul_sum]
  exact Finset.sum_comm

omit [Fintype V] in
theorem positive_law_tight_cut (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) (S : Finset V) (hS : Odd S.card)
    (ht : G.cutMass (G.mean p) S = 1) {M : G.Matching} (hM : p M ≠ 0) :
    G.cutMass (G.indicator M) S = 1 := by
  have hl (N : G.Matching) : 0 ≤ G.cutMass (G.indicator N) S - 1 :=
    sub_nonneg.mpr ((G.indicator_mem_constraintPolytope N).2.2 S hS)
  have heq : ∑ N, p N * (G.cutMass (G.indicator N) S - 1) = 0 := by
    simp only [mul_sub,mul_one,Finset.sum_sub_distrib,← cutMass_mean,ht,hp.2,sub_self]
  have hz : p M * (G.cutMass (G.indicator M) S - 1) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun N _ => mul_nonneg (hp.1 N) (hl N))).mp heq M (Finset.mem_univ M)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hM)

omit [Fintype V] in
theorem expanded_push_mean (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) (q : G.Matching → ℝ) :
    (triangleExpansion G c v).mean (fiberMass q (expandMatching G c v)) =
      triangleExtension G c hc v (G.mean q) := by
  ext e
  rw [LooplessGraph.mean,fiberMass_expect]
  simp_rw [expandMatching_indicator G c hc v]
  rcases e with e | i <;> rfl

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem triangleExtension_injective (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) : Function.Injective (triangleExtension G c hc v) := by
  intro x y h
  ext e
  exact congrFun h (Sum.inl e)

omit [Fintype V] in
theorem expanded_push_feasible (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) {x : E → ℝ} {q : G.Matching → ℝ}
    (hq : q ∈ G.feasibleLaws x) :
    fiberMass q (expandMatching G c v) ∈ (triangleExpansion G c v).feasibleLaws (triangleExtension G c hc v x) := by
  exact ⟨fiberMass_mem_simplex hq.1 _,by rw [expanded_push_mean G c hc v,hq.2]⟩

omit [Fintype V] in
theorem expanded_pull_simplex (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    {p : (triangleExpansion G c v).Matching → ℝ}
    (hp : p ∈ probabilitySimplex (triangleExpansion G c v).Matching)
    (ht : (triangleExpansion G c v).cutMass ((triangleExpansion G c v).mean p) (triangleVertices v) = 1) :
    p = fiberMass (fun M => p (expandMatching G c v M)) (expandMatching G c v) ∧
    (fun M => p (expandMatching G c v M)) ∈ probabilitySimplex G.Matching := by
  have heq : fiberMass (fun M => p (expandMatching G c v M)) (expandMatching G c v) = p := by
    apply fiberMass_pullback _ _ (expandMatching_injective G c v)
    intro N hN
    by_contra hn
    exact hN (range_expandMatching_of_crossOnce G c v N (crossOnce_of_cut_eq_one G c v N
      (positive_law_tight_cut _ hp _ (triangleVertices_odd v) ht hn)))
  refine ⟨heq.symm,simplex_of_fiberMass _ _ (expandMatching_injective G c v) ?_⟩
  exact heq.symm ▸ hp

omit [Fintype V] in
theorem expanded_pull_feasible (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) {x : E → ℝ} (hx : x ∈ G.polytope)
    {p : (triangleExpansion G c v).Matching → ℝ}
    (hp : p ∈ (triangleExpansion G c v).feasibleLaws (triangleExtension G c hc v x)) :
    p = fiberMass (fun M => p (expandMatching G c v M)) (expandMatching G c v) ∧
    (fun M => p (expandMatching G c v M)) ∈ G.feasibleLaws x := by
  have ht : (triangleExpansion G c v).cutMass ((triangleExpansion G c v).mean p) (triangleVertices v) = 1 := by
    rw [hp.2,expanded_cutMass]
    exact (G.polytope_subset_constraintPolytope hx).2.1 v
  obtain ⟨heq,hq⟩ := expanded_pull_simplex G c v hp.1 ht
  refine ⟨heq,hq,triangleExtension_injective G c hc v ?_⟩
  rw [← expanded_push_mean,← heq,hp.2]

omit [Fintype V] in
theorem expansion_image_eq (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) :
    triangleExtension G c hc v '' G.polytope =
      {y | y ∈ (triangleExpansion G c v).polytope ∧
        (triangleExpansion G c v).cutMass y (triangleVertices v) = 1} := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨q,hq⟩ := (G.mem_polytope_iff x).mp hx
    refine ⟨((triangleExpansion G c v).mem_polytope_iff _).mpr
      ⟨_,expanded_push_feasible G c hc v hq⟩,?_⟩
    rw [expanded_cutMass]
    exact (G.polytope_subset_constraintPolytope hx).2.1 v
  · rintro ⟨hy,ht⟩
    obtain ⟨p,hp⟩ := ((triangleExpansion G c v).mem_polytope_iff y).mp hy
    have ht' : (triangleExpansion G c v).cutMass ((triangleExpansion G c v).mean p) (triangleVertices v) = 1 := hp.2.symm ▸ ht
    obtain ⟨heq,hq⟩ := expanded_pull_simplex G c v hp.1 ht'
    refine ⟨_,G.mean_mem_polytope hq,?_⟩
    rw [← expanded_push_mean,← heq,hp.2]

omit [Fintype V] in
theorem expansion_image_extreme (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) :
    IsExtreme ℝ (triangleExpansion G c v).polytope (triangleExtension G c hc v '' G.polytope) := by
  rw [expansion_image_eq]
  refine ⟨fun _ h => h.1, ?_⟩
  intro y hy z hz w hw hseg
  obtain ⟨a,b,ha,hb,hab,rfl⟩ := hseg
  refine ⟨hy,?_⟩
  have heq := hw.2
  rw [LooplessGraph.cutMass_linear] at heq
  have hyl := ((triangleExpansion G c v).polytope_subset_constraintPolytope hy).2.2 _ (triangleVertices_odd v)
  have hzl := ((triangleExpansion G c v).polytope_subset_constraintPolytope hz).2.2 _ (triangleVertices_odd v)
  apply le_antisymm _ hyl
  by_contra! hn
  have hpos := mul_pos ha (sub_pos.mpr hn)
  have hnonneg := mul_nonneg hb.le (sub_nonneg.mpr hzl)
  nlinarith

omit [Fintype V] in
theorem expansion_entropy (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) {x : E → ℝ} (hx : x ∈ G.polytope) :
    maxMatchingEntropy (triangleExpansion G c v) (triangleExtension G c hc v x) = maxMatchingEntropy G x := by
  have hxe : triangleExtension G c hc v x ∈ (triangleExpansion G c v).polytope :=
    (expansion_image_extreme G c hc v).subset ⟨x,hx,rfl⟩
  apply le_antisymm
  · obtain ⟨p,hp,hopt⟩ := maxMatchingEntropy_attained _ hxe
    obtain ⟨heq,hq⟩ := expanded_pull_feasible G c hc v hx hp
    rw [← hopt,heq,entropy_fiberMass_injective _ _ (expandMatching_injective G c v)]
    exact entropy_le_maxMatchingEntropy G hq
  · obtain ⟨q,hq,hopt⟩ := maxMatchingEntropy_attained G hx
    rw [← hopt,← entropy_fiberMass_injective q _ (expandMatching_injective G c v)]
    exact entropy_le_maxMatchingEntropy (triangleExpansion G c v) (expanded_push_feasible G c hc v hq)

theorem expansion_face (G : LooplessGraph V E) (c : E → Fin 3) (hc : CubicColoring G c) (v : V) :
    let H := triangleExpansion G c v
    let f := triangleExtension G c hc v
    f '' G.polytope = {y | y ∈ H.polytope ∧ H.cutMass y (triangleVertices v) = 1} ∧
    IsExtreme ℝ H.polytope (f '' G.polytope) ∧
    ∀ x ∈ G.polytope,
      minimalFace H (f x) = f '' minimalFace G x ∧
      faceDimension H (f x) = faceDimension G x ∧
      maxMatchingEntropy H (f x) = maxMatchingEntropy G x := by
  refine ⟨expansion_image_eq G c hc v,expansion_image_extreme G c hc v,?_⟩
  intro x hx
  exact ⟨(minimalFace_map _ G (triangleExtension G c hc v).toAffineMap
      (triangleExtension_injective G c hc v) (expansion_image_extreme G c hc v) hx).symm,
    (faceDimension_map _ G (triangleExtension G c hc v).toAffineMap
      (triangleExtension_injective G c hc v) (expansion_image_extreme G c hc v) hx).symm,
    expansion_entropy G c hc v hx⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem simplicity_expansion (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hG : IsSimpleLabelled G) : IsSimpleLabelled (triangleExpansion G c v) := by
  intro e f h
  rcases e with e | i <;> rcases f with f | j
  · apply congrArg Sum.inl
    apply hG e f
    rcases h with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · exact Or.inl ⟨by simpa [triangleExpansion,collapse_reattach] using congrArg (triangleCollapse v) hl,
        by simpa [triangleExpansion,collapse_reattach] using congrArg (triangleCollapse v) hr⟩
    · exact Or.inr ⟨by simpa [triangleExpansion,collapse_reattach] using congrArg (triangleCollapse v) hl,
        by simpa [triangleExpansion,collapse_reattach] using congrArg (triangleCollapse v) hr⟩
  · exfalso
    rcases h with ⟨hl,hr⟩ | ⟨hl,hr⟩ <;>
      simp only [triangleExpansion,Sum.elim_inl,Sum.elim_inr,reattach_eq_tip] at hl hr <;>
      exact G.loopless e (hl.1.trans hr.1.symm)
  · exfalso
    rcases h with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · simp only [triangleExpansion,Sum.elim_inl,Sum.elim_inr] at hl hr
      have hl' := (reattach_eq_tip v _ _ _).mp hl.symm
      have hr' := (reattach_eq_tip v _ _ _).mp hr.symm
      exact G.loopless f (hl'.1.trans hr'.1.symm)
    · simp only [triangleExpansion,Sum.elim_inl,Sum.elim_inr] at hl hr
      have hl' := (reattach_eq_tip v _ _ _).mp hl.symm
      have hr' := (reattach_eq_tip v _ _ _).mp hr.symm
      exact G.loopless f (hr'.1.trans hl'.1.symm)
  · fin_cases i <;> fin_cases j <;> simp_all [triangleExpansion,triangleTip]

end ExpansionSupport
theorem klee_cubic (n : ℕ) : CubicColoring (kleeGraph n) (kleeColor n) := by
  induction n with
  | zero =>
    intro v i
    refine ⟨i,⟨?_,rfl⟩,?_⟩
    · fin_cases v <;> simp [LooplessGraph.Incident,kleeGraph,KleeV]
    · intro e he
      exact he.2
  | succ n ih => exact cubicColoring_expansion _ _ ih _

theorem klee_cardV (n : ℕ) : Fintype.card (KleeV n) = 2 * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (KleeV n ⊕ Fin 2) = _
    rw [Fintype.card_sum,Fintype.card_fin,ih]
    omega

theorem klee_cardE (n : ℕ) : Fintype.card (KleeE n) = 3 * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (KleeE n ⊕ Fin 3) = _
    rw [Fintype.card_sum,Fintype.card_fin,ih]
    omega

theorem klee_simple_one : IsSimpleLabelled (kleeGraph 1) := by
  intro e f h
  rcases e with e | i <;> rcases f with f | j
  · fin_cases e <;> fin_cases f <;>
      simp_all [kleeGraph,kleeColor,kleeRoot,triangleExpansion,reattach,triangleTip,KleeV,KleeE]
  · fin_cases e <;> fin_cases j <;>
      simp_all [kleeGraph,kleeColor,kleeRoot,triangleExpansion,reattach,triangleTip,KleeV,KleeE]
  · fin_cases i <;> fin_cases f <;>
      simp_all [kleeGraph,kleeColor,kleeRoot,triangleExpansion,reattach,triangleTip,KleeV,KleeE]
  · fin_cases i <;> fin_cases j <;>
      simp_all [kleeGraph,kleeColor,kleeRoot,triangleExpansion,reattach,triangleTip,KleeV,KleeE]

theorem klee_simple (n : ℕ) (hn : 0 < n) : IsSimpleLabelled (kleeGraph n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => exact klee_simple_one
    | succ n => exact simplicity_expansion _ _ _ (ih (by omega))

theorem klee_graph_properties (n : ℕ) :
    Fintype.card (KleeV n) = 2 * (n + 1) ∧ Fintype.card (KleeE n) = 3 * (n + 1) ∧
    CubicColoring (kleeGraph n) (kleeColor n) ∧
    (∀ i, (kleeGraph n).IsPerfectMatching (colorEdges (kleeColor n) i)) ∧
    (∀ e, ∃! i, e ∈ colorEdges (kleeColor n) i) ∧
    (0 < n → IsSimpleLabelled (kleeGraph n)) := by
  refine ⟨klee_cardV n,klee_cardE n,klee_cubic n,fun i => colorEdges_matching _ _ (klee_cubic n) i,?_,klee_simple n⟩
  intro e
  refine ⟨kleeColor n e,by simp [colorEdges],?_⟩
  intro i hi
  exact (by simpa [colorEdges] using hi : kleeColor n e = i).symm

end MatchingEntropyBounds.Refined

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds.Refined

section ColoredSupport
variable {V : Type uV} {E : Type uE} [Fintype E] [DecidableEq V] [DecidableEq E]

omit [DecidableEq V] in
theorem colorMatching_indicator (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (i : Fin 3) : G.indicator (colorMatching G c hc i) = coloredVector c i := by
  ext e
  simp [LooplessGraph.indicator,colorMatching,colorEdges,coloredVector]

omit [DecidableEq V] [DecidableEq E] in
theorem colorMatching_injective (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) : Function.Injective (colorMatching G c hc) := by
  intro i j hij
  have he : vertexColorEdge G c hc v i ∈ (colorMatching G c hc i).val := by
    simp [colorMatching,colorEdges,(vertexColorEdge_spec G c hc v i).2]
  rw [hij] at he
  have hh : c (vertexColorEdge G c hc v i) = j := by simpa [colorMatching,colorEdges] using he
  exact (vertexColorEdge_spec G c hc v i).2.symm.trans hh

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem coloredVector_linearIndependent (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) : LinearIndependent ℝ (coloredVector c) := by
  rw [linearIndependent_iff']
  intro s w hw i hi
  have he := congrFun hw (vertexColorEdge G c hc v i)
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,coloredVector,
    (vertexColorEdge_spec G c hc v i).2,mul_ite,mul_one,mul_zero] at he
  simpa [Finset.sum_ite_eq,hi] using he

omit [DecidableEq V] in
theorem colored_uniform_mean (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) :
    G.mean (fiberMass (uniformLaw (Fin 3)) (colorMatching G c hc)) = fun _ => 1/3 := by
  ext e
  rw [LooplessGraph.mean,fiberMass_expect]
  simp_rw [colorMatching_indicator]
  simp only [uniformLaw,Fintype.card_fin,coloredVector,mul_ite,mul_one,mul_zero]
  simp [Finset.sum_ite_eq]

omit [DecidableEq E] in
theorem expanded_colorMatching (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) (i : Fin 3) :
    expandMatching G c v (colorMatching G c hc i) =
      colorMatching (triangleExpansion G c v) (expandedColor c) (cubicColoring_expansion G c hc v) i := by
  have he : c (incidentChoice G (colorMatching G c hc i) v) = i := by
    simpa [colorMatching,colorEdges] using (incidentChoice_spec G (colorMatching G c hc i) v).1
  apply Subtype.ext
  change (colorEdges c i).disjSum {c (incidentChoice G (colorMatching G c hc i) v)} =
    colorEdges (expandedColor c) i
  rw [he]
  ext e
  rcases e with e | j <;> simp! [colorEdges,expandedColor]

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem triangleExtension_colored (G : LooplessGraph V E) (c : E → Fin 3)
    (hc : CubicColoring G c) (v : V) (i : Fin 3) :
    triangleExtension G c hc v (coloredVector c i) = coloredVector (expandedColor c) i := by
  ext e
  rcases e with e | j
  · rfl
  · simp only [triangleExtension,LinearMap.coe_mk,AddHom.coe_mk,Sum.elim_inr,coloredVector,expandedColor,(vertexColorEdge_spec G c hc v j).2]
    rfl

end ColoredSupport

theorem kleeEDecEq_succ (n : ℕ) : kleeEDecEq (n+1) = inferInstanceAs (DecidableEq (KleeE n ⊕ Fin 3)) := Subsingleton.elim _ _
theorem kleeVDecEq_succ (n : ℕ) : kleeVDecEq (n+1) = inferInstanceAs (DecidableEq (KleeV n ⊕ Fin 2)) := Subsingleton.elim _ _
theorem kleeEDecEq_zero : kleeEDecEq 0 = inferInstanceAs (DecidableEq (Fin 3)) := Subsingleton.elim _ _

theorem klee_law_eq_fiber (n : ℕ) :
    kleeLaw n = fiberMass (uniformLaw (Fin 3)) (colorMatching (kleeGraph n) (kleeColor n) (klee_cubic n)) := by
  ext M
  unfold kleeLaw fiberMass
  apply Finset.sum_congr rfl
  intro i _
  have he : colorMatching (kleeGraph n) (kleeColor n) (klee_cubic n) i = M ↔
      M.val = colorEdges (kleeColor n) i := by
    rw [Subtype.ext_iff]
    exact eq_comm
  simp [he,uniformLaw]

theorem klee_law_feasible (n : ℕ) : kleeLaw n ∈ (kleeGraph n).feasibleLaws (kleeUniform n) := by
  rw [klee_law_eq_fiber]
  exact ⟨fiberMass_mem_simplex uniformLaw_simplex _,colored_uniform_mean _ _ (klee_cubic n)⟩

theorem klee_uniform_mem (n : ℕ) : kleeUniform n ∈ (kleeGraph n).polytope :=
  ((kleeGraph n).mem_polytope_iff _).mpr ⟨_,klee_law_feasible n⟩

theorem klee_entropy_law (n : ℕ) : entropy (kleeLaw n) = Real.log 3 := by
  rw [klee_law_eq_fiber,entropy_fiberMass_injective _ _ (colorMatching_injective _ _ (klee_cubic n) (kleeRoot n)),uniformLaw_entropy]
  norm_num

theorem klee_uniform_extend (n : ℕ) :
    triangleExtension (kleeGraph n) (kleeColor n) (klee_cubic n) (kleeRoot n) (kleeUniform n) = kleeUniform (n+1) := by
  ext e
  rcases e with e | i <;> rfl

theorem klee_law_expand (n : ℕ) :
    fiberMass (kleeLaw n) (expandMatching (kleeGraph n) (kleeColor n) (kleeRoot n)) = kleeLaw (n+1) := by
  rw [klee_law_eq_fiber,klee_law_eq_fiber,fiberMass_comp]
  ext M
  unfold fiberMass
  apply Finset.sum_congr rfl
  intro i _
  rw [Function.comp_apply,expanded_colorMatching _ _ (klee_cubic n)]
  rw [kleeEDecEq_succ]
  rfl

theorem klee_triangle_expand (n : ℕ) :
    triangleExtension (kleeGraph n) (kleeColor n) (klee_cubic n) (kleeRoot n) '' kleeTriangle n = kleeTriangle (n+1) := by
  rw [kleeTriangle,LinearMap.image_convexHull,← Set.range_comp,kleeTriangle]
  congr 1
  apply congrArg Set.range
  funext i
  exact triangleExtension_colored _ _ (klee_cubic n) _ i

theorem klee_zero_matching (M : (kleeGraph 0).Matching) :
    ∃ i : Fin 3, M = colorMatching (kleeGraph 0) (kleeColor 0) (klee_cubic 0) i := by
  obtain ⟨i,hi,hu⟩ := M.property (0 : Fin 2)
  refine ⟨i,Subtype.ext ?_⟩
  ext e
  have he : (kleeGraph 0).Incident (0 : Fin 2) e := Or.inl rfl
  simp only [colorMatching,colorEdges,Finset.mem_filter,Finset.mem_univ,true_and]
  change e ∈ M.val ↔ e = i
  exact ⟨fun h => hu e ⟨h,he⟩,fun h => h ▸ hi.1⟩

theorem klee_zero_polytope : (kleeGraph 0).polytope = kleeTriangle 0 := by
  unfold LooplessGraph.polytope kleeTriangle
  congr 1
  ext x
  constructor
  · rintro ⟨M,rfl⟩
    obtain ⟨i,rfl⟩ := klee_zero_matching M
    exact ⟨i,(colorMatching_indicator _ _ _ _).symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨_,colorMatching_indicator _ _ (klee_cubic 0) i⟩

theorem klee_zero_minimal : minimalFace (kleeGraph 0) (kleeUniform 0) = (kleeGraph 0).polytope := by
  apply Set.Subset.antisymm (fun _ hy => hy.1)
  intro y hy
  refine ⟨hy,?_,?_⟩
  · intro e he
    norm_num [kleeUniform] at he
  · intro S hS _
    have hcard : S.card ≤ 2 := by
      have hh := Finset.card_le_univ S
      change S.card ≤ Fintype.card (Fin 2) at hh
      simpa using hh
    have h1 : S.card = 1 := by
      obtain ⟨k,hk⟩ := hS
      omega
    obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp h1
    rw [LooplessGraph.cutMass_singleton]
    exact ((kleeGraph 0).polytope_subset_constraintPolytope hy).2.1 v

theorem klee_minimal (n : ℕ) : minimalFace (kleeGraph n) (kleeUniform n) = kleeTriangle n := by
  induction n with
  | zero => exact klee_zero_minimal.trans klee_zero_polytope
  | succ n ih =>
    have he := ((expansion_face (kleeGraph n) (kleeColor n) (klee_cubic n) (kleeRoot n)).2.2
      (kleeUniform n) (klee_uniform_mem n)).1
    rw [klee_uniform_extend,ih,klee_triangle_expand] at he
    rw [kleeEDecEq_succ,kleeVDecEq_succ]
    exact he

theorem klee_dimension (n : ℕ) : faceDimension (kleeGraph n) (kleeUniform n) = 2 := by
  rw [faceDimension,klee_minimal,kleeTriangle,affineSpan_convexHull,direction_affineSpan]
  exact (coloredVector_linearIndependent _ _ (klee_cubic n) (kleeRoot n)).affineIndependent.finrank_vectorSpan (by decide)

theorem klee_zero_mean (p : (kleeGraph 0).Matching → ℝ) (i : KleeE 0) :
    (kleeGraph 0).mean p i =
      p (colorMatching (kleeGraph 0) (kleeColor 0) (klee_cubic 0) (kleeColor 0 i)) := by
  classical
  unfold LooplessGraph.mean
  rw [Finset.sum_eq_single
    (colorMatching (kleeGraph 0) (kleeColor 0) (klee_cubic 0) (kleeColor 0 i))]
  · rw [colorMatching_indicator]
    simp [coloredVector]
  · intro M _ hM
    obtain ⟨j,rfl⟩ := klee_zero_matching M
    rw [colorMatching_indicator]
    have hij : kleeColor 0 i ≠ j := fun h => hM (congrArg _ h.symm)
    simp [coloredVector,hij]
  · simp

theorem klee_unique_law (n : ℕ) : (kleeGraph n).feasibleLaws (kleeUniform n) = {kleeLaw n} := by
  apply Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr (klee_law_feasible n))
  induction n with
  | zero =>
    intro p hp
    apply Set.mem_singleton_iff.mpr
    ext M
    obtain ⟨i,rfl⟩ := klee_zero_matching M
    have hp' : p (colorMatching (kleeGraph 0) (kleeColor 0) (klee_cubic 0) i) = 1/3 :=
      (klee_zero_mean p i).symm.trans (congrFun hp.2 i)
    rw [hp',klee_law_eq_fiber,fiberMass_injective_apply _ _
      (colorMatching_injective _ _ (klee_cubic 0) (kleeRoot 0))]
    norm_num [kleeUniform,uniformLaw]
  | succ n ih =>
    intro p hp
    have hp' : p ∈ (triangleExpansion (kleeGraph n) (kleeColor n) (kleeRoot n)).feasibleLaws
        (triangleExtension (kleeGraph n) (kleeColor n) (klee_cubic n) (kleeRoot n) (kleeUniform n)) := by
      rw [klee_uniform_extend]
      rw [kleeEDecEq_succ] at hp
      exact hp
    obtain ⟨heq,hq⟩ := expanded_pull_feasible _ _ (klee_cubic n) _ (klee_uniform_mem n) hp'
    have hh := Set.mem_singleton_iff.mp (ih hq)
    rw [hh,klee_law_expand] at heq
    exact Set.mem_singleton_iff.mpr heq

theorem klee_maxEntropy (n : ℕ) : maxMatchingEntropy (kleeGraph n) (kleeUniform n) = Real.log 3 := by
  obtain ⟨p,hp,he⟩ := maxMatchingEntropy_attained _ (klee_uniform_mem n)
  rw [klee_unique_law,Set.mem_singleton_iff] at hp
  rw [← he,hp,klee_entropy_law]

theorem klee_entropy_terms (n : ℕ) :
    entropy (kleeUniform n) = (n + 1) * Real.log 3 ∧
    complementEntropy (kleeUniform n) = 2 * (n + 1) * Real.log (3 / 2) := by
  have hF : Real.negMulLog (1/3) = Real.log 3 / 3 := by
    norm_num [Real.negMulLog,Real.log_div]
    ring
  have hB : Real.negMulLog (1-1/3) = (2/3) * Real.log (3/2) := by
    norm_num [Real.negMulLog,Real.log_div]
    ring
  constructor
  · simp only [entropy,kleeUniform,hF,Finset.sum_const,Finset.card_univ,klee_cardE,nsmul_eq_mul,
      Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    ring
  · change (∑ _ : KleeE n, Real.negMulLog (1-1/3)) = _
    simp only [hB,Finset.sum_const,Finset.card_univ,klee_cardE,nsmul_eq_mul,
      Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    ring

theorem klee_sharp_face (n : ℕ) :
    kleeUniform n ∈ (kleeGraph n).polytope ∧
    minimalFace (kleeGraph n) (kleeUniform n) = kleeTriangle n ∧
    faceDimension (kleeGraph n) (kleeUniform n) = 2 ∧
    Fintype.card (KleeE n) - faceDimension (kleeGraph n) (kleeUniform n) = 3 * (n + 1) - 2 ∧
    (kleeGraph n).feasibleLaws (kleeUniform n) = {kleeLaw n} ∧
    maxMatchingEntropy (kleeGraph n) (kleeUniform n) = Real.log 3 ∧
    entropy (kleeUniform n) = (n + 1) * Real.log 3 ∧
    complementEntropy (kleeUniform n) = 2 * (n + 1) * Real.log (3 / 2) := by
  exact ⟨klee_uniform_mem n,klee_minimal n,klee_dimension n,by rw [klee_cardE,klee_dimension],
    klee_unique_law n,klee_maxEntropy n,klee_entropy_terms n⟩

theorem coefficient_obstruction_scalar (c : ℝ)
    (hc : ∀ n : ℕ, (n+2)*Real.log 3 - c*(2*(n+2)*Real.log (3/2)) ≤ Real.log 3) :
    Real.log 3 / (2 * Real.log (3 / 2)) ≤ c := by
  have hB : 0 < 2 * Real.log (3/2) := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  by_contra! hn
  have hd : 0 < Real.log 3 - c*(2*Real.log (3/2)) := sub_pos.mpr ((lt_div_iff₀ hB).mp hn)
  obtain ⟨n,hn⟩ := exists_nat_gt (Real.log 3 / (Real.log 3 - c*(2*Real.log (3/2))))
  have hh := (div_lt_iff₀ hd).mp hn
  have hc' := hc n
  nlinarith

theorem universal_coefficient_obstruction (c : ℝ)
    (hc : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessGraph V E) (x : E → ℝ), x ∈ G.polytope →
        entropy x - c * complementEntropy x ≤ maxMatchingEntropy G x) :
    Real.log 3 / (2 * Real.log (3 / 2)) ≤ c := by
  apply coefficient_obstruction_scalar c
  intro n
  have h := hc _ _ (kleeGraph (n+1)) (kleeUniform (n+1)) (klee_uniform_mem (n+1))
  rw [(klee_entropy_terms (n+1)).1,(klee_entropy_terms (n+1)).2,klee_maxEntropy] at h
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using h

theorem simple_coefficient_obstruction (c : ℝ)
    (hc : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessGraph V E), IsSimpleLabelled G → ∀ x : E → ℝ, x ∈ G.polytope →
        entropy x - c * complementEntropy x ≤ maxMatchingEntropy G x) :
    Real.log 3 / (2 * Real.log (3 / 2)) ≤ c := by
  apply coefficient_obstruction_scalar c
  intro n
  have h := hc _ _ (kleeGraph (n+1)) (klee_simple (n+1) (by omega)) (kleeUniform (n+1)) (klee_uniform_mem (n+1))
  rw [(klee_entropy_terms (n+1)).1,(klee_entropy_terms (n+1)).2,klee_maxEntropy] at h
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using h

end MatchingEntropyBounds.Refined

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds.Refined

def obstructionGraph : LooplessGraph (Fin 8) (Fin 12) where
  left := ![0,0,0,1,1,2,2,2,3,5,5,6]
  right := ![1,3,5,4,6,3,4,7,4,6,7,7]
  loopless := by intro e; fin_cases e <;> decide

def obstructionEdges (i : Fin 5) : Finset (Fin 12) :=
  ![{0,7,8,9}, {1,4,6,10}, {2,3,5,11}, {1,3,7,9}, {2,4,7,8}] i

def obstructionUniform : Fin 12 → ℝ := fun _ => 1 / 3

def obstructionLaw : obstructionGraph.Matching → ℝ :=
  fun M => ∑ i : Fin 3, if M.val = obstructionEdges i.castSucc.castSucc then 1 / 3 else 0

theorem obstruction_simple : IsSimpleLabelled obstructionGraph := by
  unfold IsSimpleLabelled obstructionGraph
  decide

theorem obstruction_matching (i : Fin 5) : obstructionGraph.IsPerfectMatching (obstructionEdges i) := by
  unfold LooplessGraph.IsPerfectMatching LooplessGraph.Incident obstructionGraph ExistsUnique
  fin_cases i <;> decide

def obstructionMatching (i : Fin 5) : obstructionGraph.Matching := ⟨obstructionEdges i,obstruction_matching i⟩

theorem obstructionEdges_injective : Function.Injective obstructionEdges := by
  unfold Function.Injective obstructionEdges
  decide

theorem obstructionMatching_injective : Function.Injective obstructionMatching := by
  intro i j h
  exact obstructionEdges_injective (congrArg Subtype.val h)

theorem obstruction_binary_classify (a b c d e f g h i j k l : ℕ)
    (h0 : a+b+c=1) (h1 : a+d+e=1) (h2 : f+g+h=1) (h3 : b+f+i=1)
    (h4 : d+g+i=1) (h5 : c+j+k=1) (h6 : e+j+l=1) (h7 : h+k+l=1) :
    (a=1 ∧ b=0 ∧ c=0 ∧ d=0 ∧ e=0 ∧ f=0 ∧ g=0 ∧ h=1 ∧ i=1 ∧ j=1 ∧ k=0 ∧ l=0) ∨
    (a=0 ∧ b=1 ∧ c=0 ∧ d=0 ∧ e=1 ∧ f=0 ∧ g=1 ∧ h=0 ∧ i=0 ∧ j=0 ∧ k=1 ∧ l=0) ∨
    (a=0 ∧ b=0 ∧ c=1 ∧ d=1 ∧ e=0 ∧ f=1 ∧ g=0 ∧ h=0 ∧ i=0 ∧ j=0 ∧ k=0 ∧ l=1) ∨
    (a=0 ∧ b=1 ∧ c=0 ∧ d=1 ∧ e=0 ∧ f=0 ∧ g=0 ∧ h=1 ∧ i=0 ∧ j=1 ∧ k=0 ∧ l=0) ∨
    (a=0 ∧ b=0 ∧ c=1 ∧ d=0 ∧ e=1 ∧ f=0 ∧ g=0 ∧ h=1 ∧ i=1 ∧ j=0 ∧ k=0 ∧ l=0) := by
  rcases (show a = 1 ∨ b = 1 ∨ c = 1 by omega) with ha | hb | hc
  · left
    omega
  · rcases (show d = 0 ∨ d = 1 by omega) with hd | hd
    · right; left; omega
    · right; right; right; left; omega
  · rcases (show d = 0 ∨ d = 1 by omega) with hd | hd
    · right; right; right; right; omega
    · right; right; left; omega

theorem obstruction_classify (M : obstructionGraph.Matching) : ∃ i : Fin 5, M = obstructionMatching i := by
  let a : Fin 12 → ℕ := fun e => if e ∈ M.val then 1 else 0
  have hadeg (v : Fin 8) : (∑ e : Fin 12, if obstructionGraph.Incident v e then a e else 0) = 1 := by
    obtain ⟨e,he,hu⟩ := M.property v
    rw [Finset.sum_eq_single e]
    · simp [he,a]
    · intro f _ hfe
      by_cases hf : obstructionGraph.Incident v f
      · have hfm : f ∉ M.val := fun h => hfe (hu f ⟨h,hf⟩)
        simp [hf,a,hfm]
      · simp [hf]
    · simp
  have h0 := hadeg 0
  have h1 := hadeg 1
  have h2 := hadeg 2
  have h3 := hadeg 3
  have h4 := hadeg 4
  have h5 := hadeg 5
  have h6 := hadeg 6
  have h7 := hadeg 7
  simp +decide [obstructionGraph,LooplessGraph.Incident,Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 h7
  have hcases := obstruction_binary_classify (a 0) (a 1) (a 2) (a 3) (a 4) (a 5)
    (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  clear hadeg h0 h1 h2 h3 h4 h5 h6 h7
  rcases hcases with hh | hh | hh | hh | hh
  all_goals simp [a] at hh
  · refine ⟨0,Subtype.ext ?_⟩
    ext e
    fin_cases e <;> simp_all +decide
  · refine ⟨1,Subtype.ext ?_⟩
    ext e
    fin_cases e <;> simp_all +decide
  · refine ⟨2,Subtype.ext ?_⟩
    ext e
    fin_cases e <;> simp_all +decide
  · refine ⟨3,Subtype.ext ?_⟩
    ext e
    fin_cases e <;> simp_all +decide
  · refine ⟨4,Subtype.ext ?_⟩
    ext e
    fin_cases e <;> simp_all +decide

def obstructionEquiv : Fin 5 ≃ obstructionGraph.Matching :=
  Equiv.ofBijective obstructionMatching ⟨obstructionMatching_injective,
    fun M => by obtain ⟨i,hi⟩ := obstruction_classify M; exact ⟨i,hi.symm⟩⟩

def obstructionSelected (i : Fin 3) : obstructionGraph.Matching :=
  obstructionMatching (i.castSucc.castSucc)

theorem obstructionSelected_injective : Function.Injective obstructionSelected := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 5 => k.val) (obstructionMatching_injective h))

theorem obstruction_law_eq_fiber :
    obstructionLaw = fiberMass (uniformLaw (Fin 3)) obstructionSelected := by
  ext M
  unfold obstructionLaw fiberMass
  apply Finset.sum_congr rfl
  intro i _
  have he : obstructionSelected i = M ↔ M.val = obstructionEdges i.castSucc.castSucc := by
    rw [Subtype.ext_iff]
    exact eq_comm
  simp [he,uniformLaw]

theorem obstruction_law_mean : obstructionGraph.mean obstructionLaw = obstructionUniform := by
  ext e
  rw [obstruction_law_eq_fiber,LooplessGraph.mean,fiberMass_expect]
  fin_cases e <;> simp +decide [obstructionSelected,obstructionMatching,obstructionEdges,
    uniformLaw,LooplessGraph.indicator,obstructionUniform,Fin.sum_univ_succ]

theorem obstruction_law_feasible : obstructionLaw ∈ obstructionGraph.feasibleLaws obstructionUniform := by
  refine ⟨?_,obstruction_law_mean⟩
  rw [obstruction_law_eq_fiber]
  exact fiberMass_mem_simplex uniformLaw_simplex _

theorem obstruction_uniform_mem : obstructionUniform ∈ obstructionGraph.polytope :=
  (obstructionGraph.mem_polytope_iff _).mpr ⟨_,obstruction_law_feasible⟩

theorem obstruction_mean_coordinates (p : obstructionGraph.Matching → ℝ) :
    obstructionGraph.mean p =
      ![p (obstructionMatching 0), p (obstructionMatching 1) + p (obstructionMatching 3),
        p (obstructionMatching 2) + p (obstructionMatching 4),
        p (obstructionMatching 2) + p (obstructionMatching 3),
        p (obstructionMatching 1) + p (obstructionMatching 4),
        p (obstructionMatching 2), p (obstructionMatching 1),
        p (obstructionMatching 0) + p (obstructionMatching 3) + p (obstructionMatching 4),
        p (obstructionMatching 0) + p (obstructionMatching 4),
        p (obstructionMatching 0) + p (obstructionMatching 3),
        p (obstructionMatching 1), p (obstructionMatching 2)] := by
  ext e
  unfold LooplessGraph.mean
  rw [← Equiv.sum_comp obstructionEquiv]
  change (∑ i : Fin 5, p (obstructionMatching i) * obstructionGraph.indicator (obstructionMatching i) e) = _
  fin_cases e <;> simp +decide [LooplessGraph.indicator,obstructionMatching,obstructionEdges,Fin.sum_univ_succ,add_assoc]

theorem obstruction_law_values (i : Fin 5) :
    obstructionLaw (obstructionMatching i) = ![(1 : ℝ)/3,1/3,1/3,0,0] i := by
  fin_cases i <;> simp +decide [obstructionLaw,obstructionMatching,obstructionEdges,Fin.sum_univ_succ]

theorem obstruction_unique_law :
    obstructionGraph.feasibleLaws obstructionUniform = {obstructionLaw} := by
  apply Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr obstruction_law_feasible)
  intro p hp
  have hm := hp.2
  rw [obstruction_mean_coordinates] at hm
  have h0 := congrFun hm 0
  have h1 := congrFun hm 6
  have h2 := congrFun hm 5
  have h3 := congrFun hm 3
  have h4 := congrFun hm 4
  change p (obstructionMatching 0) = 1/3 at h0
  change p (obstructionMatching 1) = 1/3 at h1
  change p (obstructionMatching 2) = 1/3 at h2
  change p (obstructionMatching 2) + p (obstructionMatching 3) = 1/3 at h3
  change p (obstructionMatching 1) + p (obstructionMatching 4) = 1/3 at h4
  apply Set.mem_singleton_iff.mpr
  ext M
  obtain ⟨i,rfl⟩ := obstruction_classify M
  rw [obstruction_law_values]
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · change p (obstructionMatching 3) = 0
    linarith only [h2,h3]
  · change p (obstructionMatching 4) = 0
    linarith only [h1,h4]

theorem obstruction_entropy_law : entropy obstructionLaw = Real.log 3 := by
  rw [obstruction_law_eq_fiber,entropy_fiberMass_injective _ _ obstructionSelected_injective,uniformLaw_entropy]
  norm_num

theorem obstruction_maxEntropy : maxMatchingEntropy obstructionGraph obstructionUniform = Real.log 3 := by
  obtain ⟨p,hp,he⟩ := maxMatchingEntropy_attained _ obstruction_uniform_mem
  rw [obstruction_unique_law,Set.mem_singleton_iff] at hp
  rw [← he,hp,obstruction_entropy_law]

theorem obstruction_entropy_terms :
    entropy obstructionUniform = 4 * Real.log 3 ∧
    complementEntropy obstructionUniform = 8 * Real.log (3/2) := by
  have hF : Real.negMulLog (1/3) = Real.log 3 / 3 := by
    norm_num [Real.negMulLog,Real.log_div]
    ring
  have hB : Real.negMulLog (1-1/3) = (2/3) * Real.log (3/2) := by
    norm_num [Real.negMulLog,Real.log_div]
    ring
  constructor
  · simp only [entropy,obstructionUniform,hF,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  · change (∑ _ : Fin 12, Real.negMulLog (1-1/3)) = _
    simp only [hB,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring

theorem obstruction_logarithms :
    entropy obstructionUniform - complementEntropy obstructionUniform = 4 * Real.log (4/3) ∧
    entropy obstructionUniform - complementEntropy obstructionUniform -
      maxMatchingEntropy obstructionGraph obstructionUniform = Real.log (256/243) := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 8 using 1 <;> norm_num
  have h243 : Real.log 243 = 5 * Real.log 3 := by
    convert Real.log_pow (3 : ℝ) 5 using 1 <;> norm_num
  rw [obstruction_entropy_terms.1,obstruction_entropy_terms.2,obstruction_maxEntropy]
  norm_num [Real.log_div,h4,h256,h243]
  constructor <;> ring

theorem eight_vertex_obstruction :
    IsSimpleLabelled obstructionGraph ∧
    (∀ M : obstructionGraph.Matching, ∃! i : Fin 5, M.val = obstructionEdges i) ∧
    (∀ i : Fin 5, obstructionGraph.IsPerfectMatching (obstructionEdges i)) ∧
    Fintype.card obstructionGraph.Matching = 5 ∧
    obstructionUniform ∈ obstructionGraph.polytope ∧
    obstructionGraph.feasibleLaws obstructionUniform = {obstructionLaw} ∧
    maxMatchingEntropy obstructionGraph obstructionUniform = Real.log 3 ∧
    entropy obstructionUniform - complementEntropy obstructionUniform = 4 * Real.log (4 / 3) ∧
    entropy obstructionUniform - complementEntropy obstructionUniform -
      maxMatchingEntropy obstructionGraph obstructionUniform = Real.log (256 / 243) ∧
    0 < Real.log (256 / 243) := by
  refine ⟨obstruction_simple,?_,obstruction_matching,?_,obstruction_uniform_mem,
    obstruction_unique_law,obstruction_maxEntropy,obstruction_logarithms.1,
    obstruction_logarithms.2,Real.log_pos (by norm_num)⟩
  · intro M
    obtain ⟨i,rfl⟩ := obstruction_classify M
    refine ⟨i,rfl,?_⟩
    intro j hj
    exact (obstructionEdges_injective hj).symm
  · exact (Fintype.card_congr obstructionEquiv).symm.trans (Fintype.card_fin 5)

end MatchingEntropyBounds.Refined

end

end OAI
end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter


namespace MatchingEntropyBounds.Refined

inductive KleeConstruction : (n : ℕ) → LooplessGraph (KleeV n) (KleeE n) → Prop
  | base : KleeConstruction 0 (kleeGraph 0)
  | expand {n : ℕ} {G : LooplessGraph (KleeV n) (KleeE n)}
      (previous : KleeConstruction n G) (v : KleeV n) :
      KleeConstruction (n+1) (triangleExpansion G (kleeColor n) v)

def coloredLaw {W : Type uW} {D : Type uD} [Fintype D] [DecidableEq W] [DecidableEq D]
    (G : LooplessGraph W D) (c : D → Fin 3) : G.Matching → ℝ :=
  fun M => ∑ i : Fin 3, if M.val = colorEdges c i then 1 / 3 else 0

section ColoredLaws
variable {W : Type uW} {D : Type uD} [Fintype W] [Fintype D] [DecidableEq W] [DecidableEq D]

omit [Fintype W] in
theorem colored_law_eq_fiber (G : LooplessGraph W D) (c : D → Fin 3) (hc : CubicColoring G c) :
    coloredLaw G c = fiberMass (uniformLaw (Fin 3)) (colorMatching G c hc) := by
  ext M
  unfold coloredLaw fiberMass
  apply Finset.sum_congr rfl
  intro i _
  have he : colorMatching G c hc i = M ↔ M.val = colorEdges c i := by
    rw [Subtype.ext_iff]
    exact eq_comm
  simp [he,uniformLaw]

omit [Fintype W] in
theorem colored_law_feasible (G : LooplessGraph W D) (c : D → Fin 3) (hc : CubicColoring G c) :
    coloredLaw G c ∈ G.feasibleLaws (fun _ => 1/3) := by
  rw [colored_law_eq_fiber G c hc]
  exact ⟨fiberMass_mem_simplex uniformLaw_simplex _,colored_uniform_mean G c hc⟩

omit [Fintype W] in
theorem colored_uniform_mem (G : LooplessGraph W D) (c : D → Fin 3) (hc : CubicColoring G c) :
    (fun _ => 1/3) ∈ G.polytope :=
  (G.mem_polytope_iff _).mpr ⟨_,colored_law_feasible G c hc⟩

omit [Fintype W] in
theorem colored_entropy_law (G : LooplessGraph W D) (c : D → Fin 3) (hc : CubicColoring G c) (v : W) :
    entropy (coloredLaw G c) = Real.log 3 := by
  rw [colored_law_eq_fiber G c hc,entropy_fiberMass_injective _ _
    (colorMatching_injective G c hc v),uniformLaw_entropy]
  norm_num

omit [Fintype W] in
theorem colored_law_expand (G : LooplessGraph W D) (c : D → Fin 3) (hc : CubicColoring G c) (v : W) :
    fiberMass (coloredLaw G c) (expandMatching G c v) =
      coloredLaw (triangleExpansion G c v) (expandedColor c) := by
  rw [colored_law_eq_fiber G c hc,
    colored_law_eq_fiber _ _ (cubicColoring_expansion G c hc v),fiberMass_comp]
  ext M
  unfold fiberMass
  apply Finset.sum_congr rfl
  intro i _
  rw [Function.comp_apply,expanded_colorMatching G c hc v]

omit [Fintype W] in
theorem colored_unique_expansion (G : LooplessGraph W D) (c : D → Fin 3) (hc : CubicColoring G c) (v : W)
    (hu : G.feasibleLaws (fun _ => 1/3) = {coloredLaw G c}) :
    (triangleExpansion G c v).feasibleLaws (fun _ => 1/3) =
      {coloredLaw (triangleExpansion G c v) (expandedColor c)} := by
  apply Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr
    (colored_law_feasible _ _ (cubicColoring_expansion G c hc v)))
  intro p hp
  have he : triangleExtension G c hc v (fun _ => 1/3) = fun _ => 1/3 := by
    ext e
    cases e <;> rfl
  rw [← he] at hp
  obtain ⟨hp',hq⟩ := expanded_pull_feasible G c hc v (colored_uniform_mem G c hc) hp
  rw [hu,Set.mem_singleton_iff] at hq
  rw [hq,colored_law_expand G c hc v] at hp'
  exact Set.mem_singleton_iff.mpr hp'

omit [Fintype W] [Fintype D] [DecidableEq W] [DecidableEq D] in
theorem colored_triangle_expansion (G : LooplessGraph W D) (c : D → Fin 3) (hc : CubicColoring G c) (v : W) :
    triangleExtension G c hc v '' convexHull ℝ (Set.range (coloredVector c)) =
      convexHull ℝ (Set.range (coloredVector (expandedColor c))) := by
  rw [LinearMap.image_convexHull,← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext i
  exact triangleExtension_colored G c hc v i

theorem colored_minimal_expansion (G : LooplessGraph W D) (c : D → Fin 3) (hc : CubicColoring G c) (v : W)
    (hm : minimalFace G (fun _ => 1/3) = convexHull ℝ (Set.range (coloredVector c))) :
    minimalFace (triangleExpansion G c v) (fun _ => 1/3) =
      convexHull ℝ (Set.range (coloredVector (expandedColor c))) := by
  have hh := ((expansion_face G c hc v).2.2 _ (colored_uniform_mem G c hc)).1
  have he : triangleExtension G c hc v (fun _ => 1/3) = fun _ => 1/3 := by
    ext e
    cases e <;> rfl
  rw [he,hm,colored_triangle_expansion G c hc v] at hh
  exact hh
end ColoredLaws

theorem klee_generated_cubic {n : ℕ} {G : LooplessGraph (KleeV n) (KleeE n)}
    (hG : KleeConstruction n G) : CubicColoring G (kleeColor n) := by
  induction hG with
  | base => exact klee_cubic 0
  | expand _ v ih => exact cubicColoring_expansion _ _ ih v

theorem klee_generated_minimal {n : ℕ} {G : LooplessGraph (KleeV n) (KleeE n)}
    (hG : KleeConstruction n G) : minimalFace G (kleeUniform n) = kleeTriangle n := by
  induction hG with
  | base => exact klee_minimal 0
  | @expand n G prev v ih =>
    rw [kleeEDecEq_succ,kleeVDecEq_succ]
    exact colored_minimal_expansion G (kleeColor n) (klee_generated_cubic prev) v ih

theorem klee_generated_unique {n : ℕ} {G : LooplessGraph (KleeV n) (KleeE n)}
    (hG : KleeConstruction n G) : G.feasibleLaws (kleeUniform n) = {coloredLaw G (kleeColor n)} := by
  induction hG with
  | base => exact klee_unique_law 0
  | @expand n G prev v ih =>
    rw [kleeEDecEq_succ,kleeVDecEq_succ]
    exact colored_unique_expansion G (kleeColor n) (klee_generated_cubic prev) v ih

theorem klee_initial_expansion_simple (v : KleeV 0) :
    IsSimpleLabelled (triangleExpansion (kleeGraph 0) (kleeColor 0) v) := by
  fin_cases v
  · exact klee_simple_one
  · intro e f h
    rcases e with e | i <;> rcases f with f | j
    · fin_cases e <;> fin_cases f <;>
        simp_all [kleeGraph,kleeColor,triangleExpansion,reattach,triangleTip,KleeV,KleeE]
    · fin_cases e <;> fin_cases j <;>
        simp_all [kleeGraph,kleeColor,triangleExpansion,reattach,triangleTip,KleeV,KleeE]
    · fin_cases i <;> fin_cases f <;>
        simp_all [kleeGraph,kleeColor,triangleExpansion,reattach,triangleTip,KleeV,KleeE]
    · fin_cases i <;> fin_cases j <;>
        simp_all [kleeGraph,kleeColor,triangleExpansion,reattach,triangleTip,KleeV,KleeE]

theorem klee_generated_simple {n : ℕ} {G : LooplessGraph (KleeV n) (KleeE n)}
    (hG : KleeConstruction n G) (hn : 1 ≤ n) : IsSimpleLabelled G := by
  induction hG with
  | base => omega
  | @expand n G prev v ih =>
    by_cases hz : n = 0
    · subst n
      cases prev
      exact klee_initial_expansion_simple v
    · exact simplicity_expansion G _ v (ih (by omega))

theorem klee_all_expansions (n : ℕ) (G : LooplessGraph (KleeV n) (KleeE n))
    (hG : KleeConstruction n G) :
    Fintype.card (KleeV n) = 2 * (n+1) ∧
    Fintype.card (KleeE n) = 3 * (n+1) ∧
    CubicColoring G (kleeColor n) ∧
    (n ≥ 1 → IsSimpleLabelled G) ∧
    kleeUniform n ∈ G.polytope ∧
    minimalFace G (kleeUniform n) = kleeTriangle n ∧
    faceDimension G (kleeUniform n) = 2 ∧
    Fintype.card (KleeE n) - faceDimension G (kleeUniform n) = 3 * (n+1) - 2 ∧
    G.feasibleLaws (kleeUniform n) = {coloredLaw G (kleeColor n)} ∧
    maxMatchingEntropy G (kleeUniform n) = Real.log 3 ∧
    entropy (kleeUniform n) = (n+1) * Real.log 3 ∧
    complementEntropy (kleeUniform n) = 2 * (n+1) * Real.log (3/2) := by
  have hc := klee_generated_cubic hG
  have hm : kleeUniform n ∈ G.polytope := colored_uniform_mem G (kleeColor n) hc
  have hd : faceDimension G (kleeUniform n) = 2 := by
    rw [faceDimension,klee_generated_minimal hG,kleeTriangle,affineSpan_convexHull,direction_affineSpan]
    exact (coloredVector_linearIndependent G _ hc (kleeRoot n)).affineIndependent.finrank_vectorSpan (by decide)
  refine ⟨klee_cardV n,klee_cardE n,hc,klee_generated_simple hG,hm,klee_generated_minimal hG,
    hd,by rw [klee_cardE,hd],klee_generated_unique hG,?_,klee_entropy_terms n⟩
  obtain ⟨p,hp,he⟩ := maxMatchingEntropy_attained G hm
  rw [klee_generated_unique hG,Set.mem_singleton_iff] at hp
  rw [← he,hp,colored_entropy_law G _ hc (kleeRoot n)]

end MatchingEntropyBounds.Refined

end

end OAI
end
end

section
section
/-!
# Sharp analytic bounds for perfect-matching entropy

For a finite loopless labelled multigraph on `2m` vertices, with `m ≥ 1` and a perfect
matching, every point of the matching polytope satisfies
`F - (2 - 2 / m) * B ≤ H ≤ F`. Here `F` and `B` are the coordinate entropy and
complement entropy with natural logarithms, and `H` is the attained supremum of entropy
over all perfect-matching laws with the prescribed mean.

The development includes the odd-cut description of the matching polytope, sharp face
rank bounds, minimal faces, fractional and connected-component reductions, attained
entropy and weighted partition objectives, matching counts, degenerate cases, colored
triangle-expansion families, and concrete coefficient obstructions.
-/
end
end

theorem solution : type_of% @OAI.MatchingEntropyBounds.Refined.pointwise_entropy_oai := @OAI.MatchingEntropyBounds.Refined.pointwise_entropy_oai
