-- Prove2me | solution 1 for OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_correlation_forces_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:53:40.799626+00:00
-- url     : https://prove2.me/submissions/d8c6e111-56b7-4034-8f55-142cdfb542a5

import Mathlib
import Definitions.Def_OAIQ3Ro002
import Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_slot_conditional_exactness

section
-- module Solutions.OAIQ3_Rok.Compat
attribute [-instance] _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_HilbertCodes
attribute [-instance] _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  (κ : Kernel U Y) [IsMarkovKernel κ]

namespace HilbertCode
variable {κ}
lemma measurable_base : Measurable (base (κ := κ)) := measurable_fst.comp measurable_subtype_coe

end HilbertCode
end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  {κ : Kernel U Y} [IsMarkovKernel κ]

namespace HilbertCode

lemma measurable_distance : Measurable (fun p : HilbertCode κ × HilbertCode κ => distance p.1 p.2) := by
  let ξ : Kernel (HilbertCode κ × HilbertCode κ) Y := κ.comap (fun p : HilbertCode κ × HilbertCode κ => p.1.base)
    (measurable_base.comp measurable_fst)
  have hf : StronglyMeasurable (fun p : (HilbertCode κ × HilbertCode κ) × Y =>
      inner ℂ (representative (p.1.1,p.2)-representative (p.1.2,p.2))
        (representative (p.1.1,p.2)-representative (p.1.2,p.2))) := by
    have h₁ : Measurable (fun p : (HilbertCode κ × HilbertCode κ) × Y => representative (p.1.1,p.2)) := (measurable_representative (κ := κ)).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have h₂ : Measurable (fun p : (HilbertCode κ × HilbertCode κ) × Y => representative (p.1.2,p.2)) := (measurable_representative (κ := κ)).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    exact (h₁.sub h₂).stronglyMeasurable.inner (h₁.sub h₂).stronglyMeasurable
  exact Real.continuous_sqrt.measurable.comp
    (Complex.continuous_re.measurable.comp (hf.integral_kernel_prod_right (κ := ξ) (f := fun p y =>
      inner ℂ (representative (p.1,y)-representative (p.2,y))
        (representative (p.1,y)-representative (p.2,y)))).measurable)
end HilbertCode

lemma measurable_hilbert_encode {V : Type*} [MeasurableSpace V]
    (u : V → U) (hu : Measurable u) (s : ∀ v, Lp ℂ 2 (κ (u v)))
    (f : V × Y → ℂ) (hf : Measurable f)
    (he : ∀ v, (s v : Y → ℂ) =ᵐ[κ (u v)] (fun y => f (v,y))) :
    Measurable (fun v => HilbertCode.encode (u v) (s v)) := by
  apply Measurable.subtype_mk
  apply hu.prodMk
  apply Measurable.of_eval
  intro n
  have hdist : (fun v => dist (s v) (hilbertTests (κ (u v)) n)) =
      fun v => Real.sqrt (Complex.re (∫ y,
        inner ℂ (f (v,y)-hilbertTestFunction (hilbertTestKeys n) y)
          (f (v,y)-hilbertTestFunction (hilbertTestKeys n) y) ∂κ (u v))) := by
    funext v
    exact lp_dist_of_representatives _ _ _ _ (he v) (hilbertTestVector_coe _ _)
  change Measurable (fun v => dist (s v) (hilbertTests (κ (u v)) n))
  rw [hdist]
  have hh := hf.sub ((hilbertTestFunction_measurable (hilbertTestKeys n)).comp measurable_snd)
  exact Real.continuous_sqrt.measurable.comp
    (Complex.continuous_re.measurable.comp
      ((hh.stronglyMeasurable.inner hh.stronglyMeasurable).integral_kernel_prod_right
        (κ := κ.comap u hu)).measurable)
end

section
open MeasureTheory MeasurableSpace Set
variable {P T : Type*} [MeasurableSpace P] [CountablySeparated P]
  [MeasurableSpace T] [StandardBorelSpace T]

lemma borel_injective_cover_branches (p : T → P) (hp : Measurable p)
    (U : ℕ → Set T) (hU : ∀ n, MeasurableSet (U n))
    (hcover : (⋃ n, U n) = Set.univ)
    (hinj : ∀ n, Set.InjOn p (U n)) :
    ∃ C : ℕ → Set T, (∀ n, MeasurableSet (C n)) ∧
      (⋃ n, C n) = Set.univ ∧ Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      (∀ n, MeasurableEmbedding (fun x : C n => p x)) := by
  refine ⟨disjointed U, fun n => MeasurableSet.disjointed hU n, ?_, disjoint_disjointed U, ?_⟩
  · rwa [iUnion_disjointed]
  · intro n
    let : StandardBorelSpace ↥(disjointed U n) := MeasurableSet.standardBorel (MeasurableSet.disjointed hU n)
    apply (hp.comp measurable_subtype_coe).measurableEmbedding
    intro x y hxy
    apply Subtype.ext
    exact hinj n (disjointed_subset U n x.property) (disjointed_subset U n y.property) hxy
end

namespace HilbertCode
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ]

lemma measurable_coefficient (n : ℕ) : Measurable (fun p : HilbertCode κ => coefficient p n) := by
  have hh : StronglyMeasurable (fun p : HilbertCode κ × Y =>
      inner ℂ (hilbertTestFunction (hilbertTestKeys n) p.2) (representative p)) :=
    ((hilbertTestFunction_measurable _).comp measurable_snd).stronglyMeasurable.inner
      measurable_representative.stronglyMeasurable
  exact (hh.integral_kernel_prod_right (κ := κ.comap base measurable_base)
    (f := fun p y => inner ℂ (hilbertTestFunction (hilbertTestKeys n) y) (representative (p,y)))).measurable

lemma measurableSet_isCanonical : MeasurableSet {p : HilbertCode κ | IsCanonical p} := by
  simp only [IsCanonical,RayCanonical,←coefficient_eq,Set.ofPred_exists,Set.ofPred_and,Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
      measurableSet_eq_fun (measurable_coefficient m) measurable_const
  · exact (measurableSet_lt measurable_const (Complex.continuous_re.measurable.comp (measurable_coefficient n))).inter
      (measurableSet_eq_fun (Complex.continuous_im.measurable.comp (measurable_coefficient n)) measurable_const)

lemma measurableSet_isUnimodular : MeasurableSet {p : HilbertCode κ | IsUnimodular p} := by
  have ht : MeasurableSet {p : HilbertCode κ × Y | ‖representative p‖ ≠ 1} :=
    (measurableSet_eq_fun measurable_representative.norm measurable_const).compl
  have hm := Kernel.measurable_kernel_prodMk_left (κ := κ.comap base measurable_base) ht
  exact measurableSet_eq_fun hm measurable_const

lemma distance_le_codes (p q : HilbertCode κ) (he : p.base = q.base) (n : ℕ) :
    distance p q ≤ p.code n + q.code n := by
  rcases p with ⟨⟨u,a⟩,ha⟩
  rcases q with ⟨⟨v,b⟩,hb⟩
  change u = v at he
  subst v
  let p : HilbertCode κ := ⟨(u,a),ha⟩
  let q : HilbertCode κ := ⟨(u,b),hb⟩
  change distance p q ≤ p.code n + q.code n
  have hp : encode u p.decode = p := encode_decode p
  have hq : encode u q.decode = q := encode_decode q
  have hd : distance p q = dist p.decode q.decode := by
    exact (congrArg₂ distance hp hq).symm.trans (distance_encode u
      (show Lp ℂ 2 (κ u) from p.decode) (show Lp ℂ 2 (κ u) from q.decode))
  rw [hd]
  rw [←decode_dist p n,←decode_dist q n]
  exact (dist_triangle _ (hilbertTests (κ u) n) _).trans_eq (by rw [dist_comm (hilbertTests (κ u) n) q.decode]; rfl)
end HilbertCode

namespace HilbertCode

open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace ComplexConjugate


variable {U Y P T : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ]
  [MeasurableSpace P] [MeasurableSpace.CountablySeparated P]
  [MeasurableSpace T] [StandardBorelSpace T]

lemma separated_branches (p : T → P) (hp : Measurable p)
    (v : T → HilbertCode κ) (hv : Measurable v)
    (hb : ∀ x y, p x = p y → (v x).base = (v y).base)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x y, p x = p y → x ≠ y → δ ≤ distance (v x) (v y)) :
    ∃ C : ℕ → Set T, (∀ n, MeasurableSet (C n)) ∧
      (⋃ n, C n) = Set.univ ∧ Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      (∀ n, MeasurableEmbedding (fun x : C n => p x)) := by
  let B : ℕ → Set T := fun n => {x | (v x).code n < δ / 3}
  apply borel_injective_cover_branches p hp B
  · intro n
    exact measurableSet_lt ((measurable_code n).comp hv) measurable_const
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨n,hn⟩ := (hilbertTests_dense (κ (v x).base)).exists_dist_lt (v x).decode
      (by positivity : 0 < δ/3)
    apply Set.mem_iUnion.mpr
    refine ⟨n,?_⟩
    change (v x).code n < δ/3
    rw [←decode_dist]
    exact hn
  · intro n x hx y hy hxy
    by_contra hne
    have h := hsep x y hxy hne
    have ht := distance_le_codes (v x) (v y) (hb x y hxy) n
    change (v x).code n < δ/3 at hx
    change (v y).code n < δ/3 at hy
    linarith
end HilbertCode

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
variable {P U Y I : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

omit [StandardBorelSpace P] [StandardBorelSpace U] [DecidableEq I] in
lemma measurable_exactCodeMean : Measurable (exactCodeMean κ Λ) := by
  have hh : StronglyMeasurable (fun t : (P × (I → HilbertCode κ)) × (I → Y) =>
      ∏ i, HilbertCode.representative (t.1.2 i,t.2 i)) := by
    apply Measurable.stronglyMeasurable
    apply Finset.measurable_prod
    intro i _
    exact HilbertCode.measurable_representative.comp
      (((measurable_pi_apply i).comp measurable_fst.snd).prodMk
        ((measurable_pi_apply i).comp measurable_snd))
  exact (hh.integral_kernel_prod_right (κ := Λ.comap Prod.fst measurable_fst)
    (f := fun (t : P × (I → HilbertCode κ)) (y : I → Y) =>
      ∏ i, HilbertCode.representative (t.2 i,y i))).measurable

omit [DecidableEq I] in
omit [StandardBorelSpace P] in
lemma measurableSet_exactCodeSet (hu : Measurable u) : MeasurableSet (exactCodeSet κ Λ u) := by
  have hbase (i : I) : MeasurableSet {t : P × (I → HilbertCode κ) | (t.2 i).base = u t.1 i} :=
    measurableSet_eq_fun
      ((HilbertCode.measurable_base (κ := κ)).comp ((measurable_pi_apply i).comp measurable_snd))
      (((measurable_pi_apply i).comp hu).comp measurable_fst)
  have hcan (i : I) : MeasurableSet {t : P × (I → HilbertCode κ) |
      HilbertCode.IsCanonical (t.2 i) ∧ HilbertCode.IsUnimodular (t.2 i)} :=
    (HilbertCode.measurableSet_isCanonical.inter HilbertCode.measurableSet_isUnimodular).preimage
      ((measurable_pi_apply i).comp measurable_snd)
  have hb : MeasurableSet {t : P × (I → HilbertCode κ) | ∀ i, (t.2 i).base = u t.1 i} := by
    convert MeasurableSet.iInter hbase using 1
    all_goals try with_reducible_and_instances rfl
    ext t
    simp
  have hc : MeasurableSet {t : P × (I → HilbertCode κ) |
      ∀ i, HilbertCode.IsCanonical (t.2 i) ∧ HilbertCode.IsUnimodular (t.2 i)} := by
    convert MeasurableSet.iInter hcan using 1
    all_goals try with_reducible_and_instances rfl
    ext t
    simp
  exact hb.inter (hc.inter (measurableSet_eq_fun (measurable_exactCodeMean κ Λ).norm measurable_const))

lemma exactCodeTuple_branches (hu : Measurable u) (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) :
    ∃ C : ℕ → Set (ExactCodeTuple κ Λ u), (∀ n, MeasurableSet (C n)) ∧
      (⋃ n, C n) = Set.univ ∧ Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      (∀ n, MeasurableEmbedding (fun x : C n => x.1.1.1)) := by
  let : StandardBorelSpace (ExactCodeTuple κ Λ u) :=
    (measurableSet_exactCodeSet κ Λ u hu).standardBorel
  obtain ⟨i₀⟩ : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  refine HilbertCode.separated_branches (fun t : ExactCodeTuple κ Λ u => t.1.1)
    measurable_subtype_coe.fst (fun t => t.1.2 i₀)
    ((measurable_pi_apply i₀).comp measurable_subtype_coe.snd) ?_ 1 zero_lt_one ?_
  · intro x y hxy
    exact (x.property.1 i₀).trans ((congrArg (fun p => u p i₀) hxy).trans (y.property.1 i₀).symm)
  · intro x y hxy hne
    have hb i : (x.1.2 i).base = (y.1.2 i).base :=
      (x.property.1 i).trans ((congrArg (fun p => u p i) hxy).trans (y.property.1 i).symm)
    have hmp i : MeasurePreserving (fun z : I → Y => z i) (Λ x.1.1) (κ (x.1.2 i).base) := by
      rw [x.property.1 i]
      exact hm x.1.1 i
    have hymean : ‖exactCodeMean κ Λ (x.1.1,y.1.2)‖ = 1 := by
      rw [show (x.1.1,y.1.2) = y.1 from Prod.ext hxy rfl]
      exact y.property.2.2
    rcases HilbertCode.exact_codes_dichotomy hk (Λ x.1.1) x.1.2 y.1.2 hb
      x.property.2.1 y.property.2.1 hmp (hind x.1.1) x.property.2.2 hymean with he | hd
    · exact (hne (Subtype.ext (Prod.ext hxy he))).elim
    · exact hd i₀
end

section
open MeasureTheory Set Function
variable {P T Z : Type*} [MeasurableSpace P] [MeasurableSpace T] [MeasurableSpace Z]

lemma measurable_branch_sections (f : T → P) (g : T → Z) (hg : Measurable g)
    (d : P → Z) (hd : Measurable d) (C : ℕ → Set T)
    (hcover : (⋃ n, C n) = Set.univ)
    (hemb : ∀ n, MeasurableEmbedding (fun x : C n => f x)) :
    ∃ (D : ℕ → Set P) (s : ℕ → P → Z),
      (∀ n, MeasurableSet (D n)) ∧ (∀ n, Measurable (s n)) ∧
      (∀ n p, p ∉ D n → s n p = d p) ∧
      (∀ n p, p ∈ D n → ∃ t, f t = p ∧ s n p = g t) ∧
      (∀ t, ∃ n, f t ∈ D n ∧ s n (f t) = g t) := by
  let F (n : ℕ) : C n → P := fun x => f x
  let D (n : ℕ) : Set P := Set.range (F n)
  let s (n : ℕ) := Function.extend (F n) (fun t => g t) d
  refine ⟨D,s,fun n => (hemb n).measurableSet_range,?_,?_,?_,?_⟩
  · intro n
    exact (hemb n).measurable_extend (hg.comp measurable_subtype_coe) hd
  · intro n p hp
    exact Function.extend_apply' _ _ p hp
  · intro n p hp
    obtain ⟨t,rfl⟩ := hp
    exact ⟨t,rfl,(hemb n).injective.extend_apply _ _ t⟩
  · intro t
    have ht : t ∈ ⋃ n, C n := by rw [hcover]; trivial
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp ht
    exact ⟨n,⟨⟨t,hn⟩,rfl⟩,(hemb n).injective.extend_apply _ _ ⟨t,hn⟩⟩

end

section
open MeasureTheory ProbabilityTheory Set Topology
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

lemma rationalSpanTest_append (v : ℕ → H) (s t : RationalSpanKey) :
    rationalSpanTest v (s ++ t) = rationalSpanTest v s + rationalSpanTest v t := by
  simp [rationalSpanTest]

lemma closure_rationalSpanTest (v : ℕ → H) :
    closure (Set.range (rationalSpanTest v)) =
      ((Submodule.span ℂ (Set.range v)).topologicalClosure : Set H) := by
  let S : AddSubmonoid H := {
    carrier := Set.range (rationalSpanTest v)
    zero_mem' := ⟨[],by simp [rationalSpanTest]⟩
    add_mem' := by
      rintro _ _ ⟨s,rfl⟩ ⟨t,rfl⟩
      exact ⟨s ++ t,rationalSpanTest_append v s t⟩ }
  let D := S.topologicalClosure
  have hd : IsClosed (D : Set H) := AddSubmonoid.isClosed_topologicalClosure S
  apply Set.Subset.antisymm
  · apply closure_minimal _ (Submodule.isClosed_topologicalClosure _)
    rintro _ ⟨t,rfl⟩
    apply Submodule.le_topologicalClosure
    induction t with
    | nil => exact Submodule.zero_mem _
    | cons p t ih =>
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨p.2,rfl⟩)) ih
  · have hsingle (n : ℕ) (c : ℂ) : c • v n ∈ D := by
      refine rationalComplex_dense.induction_on c
        (hd.preimage (continuous_id.smul continuous_const)) ?_
      intro q
      apply (show (S : Set H) ⊆ D from subset_closure)
      exact ⟨[(q,n)],by simp [rationalSpanTest]⟩
    apply closure_minimal _ hd
    intro w hw
    have h : ∀ c : ℂ, c • w ∈ D := by
      induction hw using Submodule.span_induction with
      | mem x hx => obtain ⟨n,rfl⟩ := hx; exact hsingle n
      | zero => intro c; simp only [smul_zero]; exact D.zero_mem
      | add x y hx hy ihx ihy =>
        intro c
        simpa only [smul_add] using D.add_mem (ihx c) (ihy c)
      | smul a x hx ih => intro c; simpa only [smul_smul] using ih (c*a)
    simpa using h 1

variable {P U Y : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ]
  {u : P → U}

namespace HilbertCode

lemma encode_atBase (q : HilbertCode κ) (a : U) (h : q.base = a) :
    encode a (atBase q a h) = q := by
  subst a
  exact encode_decode q
end HilbertCode

lemma MeasurableSection.zero (hu : Measurable u) :
    MeasurableSection (κ := κ) (u := u) (fun _ => 0) := by
  exact measurable_hilbert_encode u hu _ (fun _ => 0) measurable_const
    (fun _ => Lp.coeFn_zero _ _ _)

lemma MeasurableSection.add {v w : ∀ p, Lp ℂ 2 (κ (u p))}
    (hv : MeasurableSection v) (hw : MeasurableSection w) :
    MeasurableSection (fun p => v p + w p) := by
  have hu : Measurable u := HilbertCode.measurable_base.comp hv
  let f : P × Y → ℂ := fun py => HilbertCode.representative (HilbertCode.encode (u py.1) (v py.1),py.2)
  let g : P × Y → ℂ := fun py => HilbertCode.representative (HilbertCode.encode (u py.1) (w py.1),py.2)
  have hf : Measurable f := HilbertCode.measurable_representative.comp ((hv.comp measurable_fst).prodMk measurable_snd)
  have hg : Measurable g := HilbertCode.measurable_representative.comp ((hw.comp measurable_fst).prodMk measurable_snd)
  refine measurable_hilbert_encode u hu _ (f+g) (hf.add hg) ?_
  intro p
  filter_upwards [Lp.coeFn_add (v p) (w p),
    HilbertCode.representative_eq_decode (HilbertCode.encode (u p) (v p)),
    HilbertCode.representative_eq_decode (HilbertCode.encode (u p) (w p))] with y ha hv hw
  simp only [HilbertCode.decode_encode] at hv hw
  rw [ha]
  change (v p) y + (w p) y = _
  exact congrArg₂ (fun a b : ℂ => a+b) hv.symm hw.symm

lemma MeasurableSection.smul {v : ∀ p, Lp ℂ 2 (κ (u p))}
    (hv : MeasurableSection v) (c : ℂ) : MeasurableSection (fun p => c • v p) := by
  have hu : Measurable u := HilbertCode.measurable_base.comp hv
  let f : P × Y → ℂ := fun py => c * HilbertCode.representative (HilbertCode.encode (u py.1) (v py.1),py.2)
  have hf : Measurable f := measurable_const.mul (HilbertCode.measurable_representative.comp
    ((hv.comp measurable_fst).prodMk measurable_snd))
  refine measurable_hilbert_encode u hu _ f hf ?_
  intro p
  filter_upwards [Lp.coeFn_smul c (v p),
    HilbertCode.representative_eq_decode (HilbertCode.encode (u p) (v p))] with y ha hv
  simp only [HilbertCode.decode_encode] at hv
  rw [ha]
  change c * (v p) y = _
  exact congrArg (c * ·) hv.symm

lemma MeasurableSection.rationalSpanTest (hu : Measurable u)
    {s : ℕ → ∀ p, Lp ℂ 2 (κ (u p))} (hs : ∀ n, MeasurableSection (s n))
    (t : RationalSpanKey) : MeasurableSection (fun p => rationalSpanTest (fun n => s n p) t) := by
  induction t with
  | nil => exact MeasurableSection.zero hu
  | cons p t ih => exact ((hs p.2).smul _).add ih

lemma measurableSet_section_mem_span (hu : Measurable u)
    {s : ℕ → ∀ p, Lp ℂ 2 (κ (u p))} (hs : ∀ n, MeasurableSection (s n))
    {v : ∀ p, Lp ℂ 2 (κ (u p))} (hv : MeasurableSection v) :
    MeasurableSet {p | v p ∈ (Submodule.span ℂ (Set.range (fun n => s n p))).topologicalClosure} := by
  have he (p) : v p ∈ (Submodule.span ℂ (Set.range (fun n => s n p))).topologicalClosure ↔
      ∀ m : ℕ, ∃ t : RationalSpanKey,
        dist (v p) (rationalSpanTest (fun n => s n p) t) < (1 : ℝ) / (m+1) := by
    change v p ∈ ((Submodule.span ℂ (Set.range (fun n => s n p))).topologicalClosure : Set _) ↔ _
    rw [←closure_rationalSpanTest (fun n => s n p)]
    exact Metric.mem_closure_range_iff_nat
  simp_rw [he,Set.ofPred_forall,Set.ofPred_exists]
  apply MeasurableSet.iInter
  intro m
  apply MeasurableSet.iUnion
  intro t
  have hd := HilbertCode.measurable_distance.comp (hv.prodMk (MeasurableSection.rationalSpanTest hu hs t))
  have hd' : Measurable (fun p => dist (v p) (rationalSpanTest (fun n => s n p) t)) := by
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    exact (HilbertCode.distance_encode (u p) (v p) (rationalSpanTest (fun n => s n p) t)).symm
  exact measurableSet_lt hd' measurable_const
end

section
open MeasureTheory ProbabilityTheory Set
variable {P U Y I : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

lemma exactCode_sections (hu : Measurable u) (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) :
    ∃ (D : ℕ → Set P) (s : ℕ → P → I → HilbertCode κ),
      (∀ n, MeasurableSet (D n)) ∧ (∀ n, Measurable (s n)) ∧
      (∀ n p i, (s n p i).base = u p i) ∧
      (∀ n p, p ∈ D n → (p,s n p) ∈ exactCodeSet κ Λ u) ∧
      (∀ n p, p ∉ D n → s n p = fun i => HilbertCode.encode (u p i) 0) ∧
      (∀ t ∈ exactCodeSet κ Λ u, ∃ n, t.1 ∈ D n ∧ s n t.1 = t.2) := by
  let T := ExactCodeTuple κ Λ u
  obtain ⟨C,_,hcover,_,hemb⟩ := exactCodeTuple_branches κ Λ u hu hk hm hind
  let d : P → I → HilbertCode κ := fun p i => HilbertCode.encode (u p i) 0
  have hd : Measurable d := by
    apply Measurable.of_eval
    intro i
    exact MeasurableSection.zero ((measurable_pi_apply i).comp hu)
  obtain ⟨D,s,hD,hs,hzero,hhas,hevery⟩ := measurable_branch_sections
    (fun t : T => t.1.1) (fun t : T => t.1.2) measurable_subtype_coe.snd d hd C hcover hemb
  have hmem (n) (p) (hp : p ∈ D n) : (p,s n p) ∈ exactCodeSet κ Λ u := by
    obtain ⟨t,ht,hs⟩ := hhas n p hp
    rw [hs,←ht]
    exact t.property
  refine ⟨D,s,hD,hs,?_,hmem,hzero,?_⟩
  · intro n p i
    by_cases hp : p ∈ D n
    · exact (hmem n p hp).1 i
    · rw [hzero n p hp]
      rfl
  · intro t ht
    exact hevery ⟨t,ht⟩

end

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp

variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

namespace HilbertCode
variable {κ}
lemma circleLp_circleRep (q : HilbertCode κ) (hq : IsUnimodular q) :
    circleLp (κ q.base) (circleRep (κ := κ) q) (measurable_circleRep_fixed (κ := κ) q) = q.decode := by
  apply Lp.ext
  exact (circleLp_coe (κ q.base) (circleRep (κ := κ) q) (measurable_circleRep_fixed (κ := κ) q)).trans
    ((circleRep_ae (κ := κ) q hq).trans (representative_eq_decode q))
end HilbertCode

end

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Arrays
attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.columnGroupKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.columnPairKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunArrαYOfNatNatComplexMemAddSubgroupLpENNRealSubmoduleRawSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunCellComplexMemAddSubgroupLpOfNatENNRealSubmoduleSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleColumnActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleCommonActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleRowActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatCellSlotLocal _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallCellSlotTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallYRawTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYColumnCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYRowCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.rowPairKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.splitRowKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.arrayLaw_probability _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.localLaw_probability _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section

open MeasureTheory ProbabilityTheory
universe u
namespace ArrayObjects

section

attribute [instance] InitialLaws.probability

attribute [instance] Object.probability

end


end ArrayObjects

open scoped InnerProductSpace

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

namespace FiniteKernel
lemma map_eval {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    (κ : ∀ i, Kernel X (Y i)) [∀ i, IsMarkovKernel (κ i)] (i : ι) :
    (pi κ).map (Function.eval i) = κ i := by
  ext x : 1
  rw [Kernel.map_apply _ (measurable_pi_apply i)]
  exact (measurePreserving_eval (fun j => κ j x) i).map_eq
end FiniteKernel

namespace ArrayObjects.Object
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in
lemma plane_conditional (hI : 2 ≤ Fintype.card I) (n : ℕ) (a : I) :
    HasCondDistrib (plane n (Fin.last n) a) (amap M.par (n + 1))
      ((M.ownKernel n).comap (plane n (Fin.last n) a) (measurable_plane _ _ _))
      (M.law (n + 1)) := by
  have hproper : ({a} : Finset I) ≠ Finset.univ := by
    intro he
    have hc := congrArg Finset.card he
    simp only [Finset.card_singleton, Finset.card_univ] at hc
    omega
  have h := (M.planes_conditional n {a} hproper).comp_left
    (measurable_pi_apply (⟨a, Finset.mem_singleton_self a⟩ : ({a} : Finset I)))
  rw [FiniteKernel.map_eval] at h
  exact h

end ArrayObjects.Object

end

open MeasureTheory ProbabilityTheory

namespace ConditionalFibres
variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [StandardBorelSpace Y]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {u : Ω → U} {x : Ω → X} {y : Ω → Y}
  {η : Kernel U Ω} [IsMarkovKernel η] {κ : Kernel (U × X) Y} [IsMarkovKernel κ]

theorem marginal (hx : Measurable x) (hη : HasCondDistrib id u η μ)
    {α : Kernel U X} [IsMarkovKernel α] (hα : HasCondDistrib x u α μ) :
    ∀ᵐ a ∂μ.map u, MeasurePreserving x (η a) (α a) := by
  let : IsMarkovKernel (η.map x) := Kernel.IsMarkovKernel.map η hx
  have he : η.map x =ᵐ[μ.map u] α :=
    Kernel.ae_eq_of_compProd_eq ((hη.comp_left hx).map_eq.symm.trans hα.map_eq)
  filter_upwards [he] with a ha
  exact ⟨hx, (Kernel.map_apply η hx a).symm.trans ha⟩

end ConditionalFibres

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Joinings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

namespace JoiningOperator

open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal


section
variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {τ : Measure Z}
  {x : Ω → X} {y : Ω → Y} {z : X → Z}

lemma pull_adjoint_pull (hx : MeasurePreserving x μ ν) :
    (pull hx).adjoint ∘L pull hx = ContinuousLinearMap.id ℂ (Lp ℂ 2 ν) := by
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (pull hx)).mp
  intro g
  exact Lp.norm_compMeasurePreserving g hx

lemma inner_operator (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (g : Lp ℂ 2 ν) (h : Lp ℂ 2 ρ) :
    inner ℂ g (operator hx hy h) = ∫ ω, inner ℂ (g (x ω)) (h (y ω)) ∂μ := by
  change inner ℂ g ((pull hx).adjoint (pull hy h)) = _
  rw [adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving g hx, Lp.coeFn_compMeasurePreserving h hy]
    with ω hg hh
  change inner ℂ (Lp.compMeasurePreserving x hx g ω) (Lp.compMeasurePreserving y hy h ω) = _
  rw [hg, hh]
  rfl

end
section

variable {Ω X Y : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y}
  {x : Ω → X} {y : Ω → Y}

lemma pull_range (hx : MeasurePreserving x μ ν) :
    LinearMap.range (pull hx).toLinearMap =
      lpMeas ℂ ℂ (MeasurableSpace.comap x inferInstance) 2 μ := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    apply mem_lpMeas_iff_aestronglyMeasurable.mpr
    have hm : StronglyMeasurable[MeasurableSpace.comap x inferInstance] (fun ω => g (x ω)) :=
      g.1.stronglyMeasurable.comp_measurable (Measurable.of_comap_le le_rfl)
    exact hm.aestronglyMeasurable.congr (Lp.coeFn_compMeasurePreserving g hx).symm
  · intro hf
    have hm := mem_lpMeas_iff_aestronglyMeasurable.mp hf
    obtain ⟨g, hg, he⟩ := hm.stronglyMeasurable_mk.exists_eq_measurable_comp
    have hfe : f =ᵐ[μ] g ∘ x := hm.ae_eq_mk.trans (Filter.Eventually.of_forall (congrFun he))
    have hLp : MemLp g 2 ν := by
      rw [← hx.map_eq]
      exact (memLp_map_measure_iff hg.aestronglyMeasurable hx.aemeasurable).mpr
        ((memLp_congr_ae hfe).mp (Lp.memLp f))
    refine ⟨hLp.toLp g, ?_⟩
    apply Lp.ext
    exact (Lp.coeFn_compMeasurePreserving (hLp.toLp g) hx).trans
      ((hx.quasiMeasurePreserving.ae_eq_comp hLp.coeFn_toLp).trans hfe.symm)

lemma pull_adjoint_projection (hx : MeasurePreserving x μ ν) (f : Lp ℂ 2 μ) :
    pull hx ((pull hx).adjoint f) =
      (condExpL2 ℂ ℂ hx.measurable.comap_le f : Lp ℂ 2 μ) := by
  let S := lpMeas ℂ ℂ (MeasurableSpace.comap x inferInstance) 2 μ
  let : Fact (MeasurableSpace.comap x inferInstance ≤ mΩ) := ⟨hx.measurable.comap_le⟩
  change _ = S.starProjection f
  apply (S.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_).symm
  · change _ ∈ lpMeas ℂ ℂ (MeasurableSpace.comap x inferInstance) 2 μ
    rw [← pull_range hx]
    exact ⟨(pull hx).adjoint f, rfl⟩
  · intro u hu
    change u ∈ lpMeas ℂ ℂ (MeasurableSpace.comap x inferInstance) 2 μ at hu
    rw [← pull_range hx] at hu
    obtain ⟨g, rfl⟩ := hu
    rw [inner_sub_left]
    change inner ℂ f (pull hx g) -
      inner ℂ (pull hx ((pull hx).adjoint f)) (pull hx g) = 0
    rw [← adjoint_inner_left, ← adjoint_inner_left]
    change inner ℂ ((pull hx).adjoint f) g -
      inner ℂ (((pull hx).adjoint ∘L pull hx) ((pull hx).adjoint f)) g = 0
    rw [pull_adjoint_pull]
    simp

lemma operator_ae_eq_condExp [IsFiniteMeasure μ]
    (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ) (h : Lp ℂ 2 ρ) :
    (fun ω => operator hx hy h (x ω)) =ᵐ[μ]
      μ[(fun ω => h (y ω)) | MeasurableSpace.comap x inferInstance] := by
  have hp := pull_adjoint_projection hx (pull hy h)
  have hc := (Lp.memLp (pull hy h)).condExpL2_ae_eq_condExp (𝕜 := ℂ) hx.measurable.comap_le
  rw [Lp.toLp_coeFn, ← hp] at hc
  exact (Lp.coeFn_compMeasurePreserving (operator hx hy h) hx).symm.trans
    (hc.trans (condExp_congr_ae (Lp.coeFn_compMeasurePreserving h hy)))


end
section

variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] [MeasurableSpace Z]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure X} {ρ : Measure Y}
  {τ : Measure Z} {x : Ω → X} {y : Ω → Y} {z : X → Z}

lemma condExp_of_kernel (hx : Measurable x) {κ : Kernel X Y} [IsMarkovKernel κ]
    (h : HasCondDistrib y x κ μ) (g : Y → ℂ) (hg : StronglyMeasurable g)
    (hgi : Integrable (fun ω => g (y ω)) μ) :
    μ[(fun ω => g (y ω)) | MeasurableSpace.comap x inferInstance] =ᵐ[μ]
      (fun ω => ∫ v, g v ∂κ (x ω)) := by
  have he : condDistrib y x μ =ᵐ[μ.map x] κ :=
    condDistrib_ae_eq_of_measure_eq_compProd h.aemeasurable_fst h.aemeasurable_snd h.map_eq
  have he' := ae_of_ae_map hx.aemeasurable he
  filter_upwards [condExp_ae_eq_integral_condDistrib hx h.aemeasurable_snd hg hgi, he']
    with ω hω heω
  exact hω.trans (by rw [heω])


end


end JoiningOperator

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_ExactLines
attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.arrayLaw_probability _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.localLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory ProbabilityTheory Set

theorem ae_map_descent {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [StandardBorelSpace Ω] [StandardBorelSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → S} (hf : Measurable f)
    {P : S → Prop} (hP : ∀ᵐ ω ∂μ, P (f ω)) : ∀ᵐ s ∂μ.map f, P s := by
  let : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  let κ := condDistrib id f μ
  have hnull : NullMeasurableSet {ω | P (f ω)} μ := by
    exact NullMeasurableSet.congr (nullMeasurableSet_univ (μ := μ))
      (by filter_upwards [hP] with ω hω; exact propext (iff_of_true trivial hω))
  obtain ⟨t,ht,htm,hte⟩ := hnull.exists_measurable_subset_ae_eq
  have hta : ∀ᵐ ω ∂μ, ω ∈ t := by
    filter_upwards [hP,hte] with ω hω he
    exact he.mpr hω
  have hgood : ∀ᵐ s ∂μ.map f, ∀ᵐ ω ∂κ s, ω ∈ t ∧ f ω = s := by
    apply Measure.ae_ae_of_ae_compProd (p := fun p : S × Ω => p.2 ∈ t ∧ f p.2 = p.1)
    change ∀ᵐ p ∂μ.map f ⊗ₘ condDistrib id f μ, p.2 ∈ t ∧ f p.2 = p.1
    rw [compProd_map_condDistrib aemeasurable_id]
    apply (ae_map_iff (hf.prodMk measurable_id).aemeasurable
      ((htm.preimage measurable_snd).inter (measurableSet_eq_fun (hf.comp measurable_snd) measurable_fst))).mpr
    filter_upwards [hta] with ω hω
    exact ⟨hω,rfl⟩
  filter_upwards [hgood] with s hs
  obtain ⟨ω,hω,he⟩ := hs.exists
  rw [←he]
  exact ht hω
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u
variable {I : Type u} [Fintype I] [retained10 : DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma slotActive_eq (i : I) (ν : Measure (Cell M i)) (p : Arr I M.U 1)
    (h : MeasurePreserving (slotCell M i) (M.ownKernel 1 p) ν) :
    slotActive M i ν p = (LinearMap.range (JoiningOperator.operator h
      (MeasurePreserving.mk (measurable_slotRest M i) rfl)).toLinearMap).topologicalClosure := by
  rw [slotActive,dite_eq_left h]

include retained10 in
lemma slotCell_marginal (hI : 2 ≤ Fintype.card I) (i : I) :
    ∀ᵐ p ∂M.parameterLaw 1, MeasurePreserving (slotCell M i) (M.ownKernel 1 p)
      (slotLocal M i (plane 0 0 i p)) := by
  let _ := retained10
  have h := ConditionalFibres.marginal (measurable_plane 0 0 i)
    (M.ownKernel_conditional 1) (M.plane_conditional hI 0 i)
  filter_upwards [h] with p hp
  exact (MeasurePreserving.mk (measurable_padCell M i) (Kernel.map_apply _ (measurable_padCell M i) _).symm).comp hp

end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory Set
section
lemma iIndepFun_map_iff_measurable {A B J C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [Fintype J] (μ : Measure A) [IsProbabilityMeasure μ]
    (f : B → J → C) (g : A → B) (hf : ∀ j, Measurable (fun b => f b j)) (hg : Measurable g) :
    iIndepFun (fun j b => f b j) (μ.map g) ↔ iIndepFun (fun j a => f (g a) j) μ := by
  let : IsProbabilityMeasure (μ.map g) := (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) hg.aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun j => (hf j).aemeasurable),
    iIndepFun_iff_map_fun_eq_pi_map (f := fun j a => f (g a) j) (fun j => ((hf j).comp hg).aemeasurable)]
  simp only [Measure.map_map (Measurable.of_eval hf) hg,
    Measure.map_map (hf _) hg]
  rfl
end
namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in
lemma slotTuple_marginal (hI : 2 ≤ Fintype.card I) (r : I) :
    ∀ᵐ p ∂M.parameterLaw 1, ∀ j,
      MeasurePreserving (fun z : I → Cell M r => z j) (slotTupleKernel M r p)
        (slotLocal M r (tupleParameter M p j)) := by
  have h (j : I) := ConditionalFibres.marginal (measurable_plane 0 0 j)
    (M.ownKernel_conditional 1) (M.plane_conditional hI 0 j)
  filter_upwards [ae_all_iff.mpr h] with p hp j
  refine ⟨measurable_pi_apply j,?_⟩
  rw [slotTupleKernel,Kernel.map_apply _ (measurable_slotTuple M r),
    Measure.map_map (measurable_pi_apply j) (measurable_slotTuple M r)]
  change (M.ownKernel 1 p).map (padCell M r ∘ plane 0 0 j) = _
  rw [←Measure.map_map (measurable_padCell M r) (measurable_plane 0 0 j),(hp j).map_eq]
  change ((M.ownKernel 0) (plane 0 0 j p)).map (padCell M r) =
    (slotLocal M r) (tupleParameter M p j)
  exact (Kernel.map_apply (M.ownKernel 0) (measurable_padCell M r) _).symm

lemma tuple_planes_product (j : I) :
    ∀ᵐ p ∂M.parameterLaw 1, MeasurePreserving (planes 0 (Finset.univ.erase j))
      (M.ownKernel 1 p)
      (Measure.pi (fun t : (Finset.univ.erase j : Finset I) =>
        M.ownKernel 0 (plane 0 0 t p))) := by
  have hproper : Finset.univ.erase j ≠ (Finset.univ : Finset I) := by
    intro he
    have := congrArg (fun s : Finset I => j ∈ s) he
    simp at this
  exact ConditionalFibres.marginal (measurable_planes _ _)
    (M.ownKernel_conditional 1) (M.planes_conditional 0 _ hproper)

lemma slotTuple_proper (r : I) :
    ∀ᵐ p ∂M.parameterLaw 1, ∀ j,
      iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
        fun z : I → Cell M r => z t) (slotTupleKernel M r p) := by
  filter_upwards [ae_all_iff.mpr (tuple_planes_product M)] with p hp j
  rw [slotTupleKernel,Kernel.map_apply _ (measurable_slotTuple M r)]
  apply (iIndepFun_map_iff_measurable (J := ↥(Finset.univ.erase j)) _ _ _ (fun t => measurable_pi_apply (t : I))
    (measurable_slotTuple M r)).mpr
  have h := iIndepFun_pi (μ := fun t : (Finset.univ.erase j : Finset I) =>
    M.ownKernel 0 (plane 0 0 t p)) (fun _ : (Finset.univ.erase j : Finset I) =>
    (measurable_padCell M r).aemeasurable)
  rw [←(hp j).map_eq] at h
  exact (iIndepFun_map_iff_measurable (M.ownKernel 1 p)
    (fun (b : ↥(Finset.univ.erase j : Finset I) → Arr I M.Y 0) t => padCell M r (b t))
    (planes 0 (Finset.univ.erase j))
    (fun t => (measurable_padCell M r).comp (measurable_pi_apply t))
    (measurable_planes 0 _)).mp h

end ArrayObjects.Object.Rolled
end

section
open MeasureTheory ProbabilityTheory Set
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U) (hu : Measurable u)

include hu in
lemma exists_good_tuple_kernel (μ : Measure P)
    (hm : ∀ᵐ p ∂μ, ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ᵐ p ∂μ, ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) :
    ∃ Λ' : Kernel P (I → Y), IsMarkovKernel Λ' ∧ Λ' =ᵐ[μ] Λ ∧
      (∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ' p) (κ (u p i))) ∧
      (∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
        fun y : I → Y => y j) (Λ' p)) := by
  classical
  let Q := fun p => (∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i))) ∧
    (∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) => fun y : I → Y => y j) (Λ p))
  have hq : ∀ᵐ p ∂μ, Q p := hm.and hind
  have hn : NullMeasurableSet {p | Q p} μ :=
    NullMeasurableSet.congr (nullMeasurableSet_univ (μ := μ))
      (by filter_upwards [hq] with p h; exact propext (iff_of_true trivial h))
  obtain ⟨D,hD,hDm,he⟩ := hn.exists_measurable_subset_ae_eq
  let L := Kernel.piecewise hDm Λ (productTupleKernel κ u hu)
  have hlm (p) (i) : MeasurePreserving (fun y : I → Y => y i) (L p) (κ (u p i)) := by
    by_cases hp : p ∈ D
    · simpa only [L,Kernel.piecewise_apply,ite_eq_left hp] using (hD hp).1 i
    · simpa only [L,Kernel.piecewise_apply,ite_eq_right hp,productTupleKernel,FiniteKernel.pi_apply,
        Kernel.comap_apply] using (measurePreserving_eval (fun i => κ (u p i)) i)
  have hli (p) (i) : iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (L p) := by
    by_cases hp : p ∈ D
    · simpa only [L,Kernel.piecewise_apply,ite_eq_left hp] using (hD hp).2 i
    · simp only [L,Kernel.piecewise_apply,ite_eq_right hp,productTupleKernel,FiniteKernel.pi_apply,Kernel.comap_apply]
      exact (iIndepFun_pi (μ := fun i => κ (u p i)) (fun _ => measurable_id.aemeasurable)).precomp
        Subtype.val_injective
  refine ⟨L,inferInstance,?_,hlm,hli⟩
  filter_upwards [hq,he] with p hp he
  exact (Kernel.piecewise_apply p).trans (ite_eq_left (he.mpr hp))
end

section
open MeasureTheory ProbabilityTheory
variable {Ω S Z : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace Z]
  [StandardBorelSpace Ω] [StandardBorelSpace S] [StandardBorelSpace Z]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Ω → S} {z : Ω → Z}
  {κ : Kernel S Z} [IsSFiniteKernel κ]
lemma conditional_ae_descent (hs : Measurable s) (hz : Measurable z)
    (hκ : HasCondDistrib z s κ μ) {P : S → Z → Prop} (hP : ∀ᵐ ω ∂μ, P (s ω) (z ω)) :
    ∀ᵐ a ∂μ.map s, ∀ᵐ b ∂κ a, P a b := by
  apply Measure.ae_ae_of_ae_compProd (p := fun p : S × Z => P p.1 p.2)
  rw [←hκ.map_eq]
  exact ae_map_descent μ (hs.prodMk hz) hP
end

section
open MeasureTheory
open scoped BigOperators
variable {I Y : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Y]
attribute [local instance] OAI.Rokhlin.instMeasurableSpaceCircle_solutions_4
local instance instBorelSpaceCircle_solutions_4 : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))

omit [MeasurableSpace Y] in
lemma circleComplete_self (i : I) (f : Y → Circle) (a : ↥(({i} : Finset I)ᶜ) → Y → Circle) :
    circleComplete i f a i = f := by funext y; simp [circleComplete]

lemma measurable_circleComplete (i : I) (f : Y → Circle) (a : ↥(({i} : Finset I)ᶜ) → Y → Circle)
    (hf : Measurable f) (ha : ∀ j, Measurable (a j)) (j : I) : Measurable (circleComplete i f a j) := by
  unfold circleComplete
  by_cases h : j = i
  · simpa only [dite_eq_left h] using hf
  · simp only [dite_eq_right h]
    exact measurable_inv.comp (ha ⟨j,by simpa using h⟩)

lemma prod_complement (i : I) (g : I → Circle) :
    (∏ j, g j) = g i * ∏ j : ↥(({i} : Finset I)ᶜ), g j := by
  rw [Fintype.prod_eq_mul_prod_compl i g,Finset.prod_coe_sort]

omit [MeasurableSpace Y] in
lemma circleComplete_prod (i : I) (f : Y → Circle) (a : ↥(({i} : Finset I)ᶜ) → Y → Circle)
    (y : I → Y) (c : Circle) (h : f (y i) = c * ∏ j, a j (y j)) :
    ∏ j, circleComplete i f a j (y j) = c := by
  rw [prod_complement i,circleComplete_self]
  have ht (j : ↥(({i} : Finset I)ᶜ)) : circleComplete i f a j (y j) = (a j (y j))⁻¹ := by
    have hj : (j : I) ≠ i := fun h => (Finset.mem_compl.mp j.property) (Finset.mem_singleton.mpr h)
    simp only [circleComplete,dite_eq_right hj]
  simp only [ht,Finset.prod_inv_distrib,h,mul_assoc,mul_inv_cancel,mul_one]

lemma prod_equation_solve (i : I) (g : I → Circle) (c : Circle) (h : ∏ j, g j = c) :
    g i = c * ∏ j : ↥(({i} : Finset I)ᶜ), (g j)⁻¹ := by
  rw [Finset.prod_inv_distrib,←h,prod_complement i,mul_assoc,mul_inv_cancel,mul_one]
end

namespace JoiningOperator
open MeasureTheory
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
  {x : Ω → X} {y : Ω → Y}
lemma circleLp_operator (hx : MeasurePreserving x μ ν) (hy : MeasurePreserving y μ ρ)
    (f : X → Circle) (g : Y → Circle) (hf : Measurable f) (hg : Measurable g)
    (he : ∀ᵐ ω ∂μ, f (x ω) = g (y ω)) :
    operator hx hy (circleLp ρ g hg) = circleLp ν f hf := by
  have hp : pull hx (circleLp ν f hf) = pull hy (circleLp ρ g hg) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (circleLp ν f hf) hx,
      Lp.coeFn_compMeasurePreserving (circleLp ρ g hg) hy,
      hx.quasiMeasurePreserving.ae (circleLp_coe ν f hf),
      hy.quasiMeasurePreserving.ae (circleLp_coe ρ g hg),he] with ω h1 h2 h3 h4 h5
    exact (h1.trans h3).trans ((congrArg ((↑) : Circle → ℂ) h5).trans (h2.trans h4).symm)
  change (pull hx).adjoint (pull hy (circleLp ρ g hg)) = _
  rw [←hp]
  exact congrArg (fun A : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν => A (circleLp ν f hf)) (pull_adjoint_pull hx)
end JoiningOperator

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
lemma HilbertCode.encode_injective {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ] (u : U) :
    Function.Injective (HilbertCode.encode (κ := κ) u) := by
  intro v w h
  apply distance_code_injective (hilbertTests_dense (κ u))
  funext n
  exact congrArg (fun a : HilbertCode κ => a.code n) h

variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

omit [DecidableEq I] [IsMarkovKernel Λ] in
lemma exactCodeSpan_congr_kernel (Λ' : Kernel P (I → Y)) [IsMarkovKernel Λ']
    (p : P) (i : I) (he : Λ p = Λ' p) :
    exactCodeSpan κ Λ u p i = exactCodeSpan κ Λ' u p i := by
  have hs : exactCodeVectors κ Λ u p i = exactCodeVectors κ Λ' u p i := by
    ext v
    simp only [exactCodeVectors, exactCodeSet, exactCodeMean, Set.mem_ofPred_eq, he]
  unfold exactCodeSpan
  rw [hs]

omit [DecidableEq I] in
lemma exactCircle_mem_codeSpan (p : P) (i : I)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    (f : I → Y → Circle) (hf : ∀ j, Measurable (f j)) (c : Circle)
    (he : ∀ᵐ y ∂Λ p, ∏ j, f j (y j) = c) (d : ℂ) :
    d • circleLp (κ (u p i)) (f i) (hf i) ∈ exactCodeSpan κ Λ u p i := by
  obtain ⟨a,b,ha,hb⟩ := normalized_exact_codes κ Λ u p hm f hf c he
  have hv : b i • circleLp (κ (u p i)) (f i) (hf i) ∈ exactCodeSpan κ Λ u p i :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨a,ha,(hb i).2⟩)
  have hn : b i ≠ 0 := by intro hz; simpa only [hz,norm_zero,zero_ne_one] using (hb i).1
  convert (exactCodeSpan κ Λ u p i).smul_mem (d * (b i)⁻¹) hv using 1
  all_goals try with_reducible_and_instances rfl
  rw [smul_smul,mul_assoc,inv_mul_cancel₀ hn,mul_one]

omit [DecidableEq I] in
lemma exactVector_circle_tuple (p : P) (i : I)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    {v : Lp ℂ 2 (κ (u p i))} (hv : v ∈ exactCodeVectors κ Λ u p i) :
    ∃ (f : I → Y → Circle) (hf : ∀ j, Measurable (f j)) (c : Circle),
      v = circleLp (κ (u p i)) (f i) (hf i) ∧ ∀ᵐ y ∂Λ p, ∏ j, f j (y j) = c := by
  obtain ⟨a,ha,hv⟩ := hv
  obtain ⟨c,hc⟩ := exactCode_circle_tuple κ Λ u hm ha
  refine ⟨fun j => HilbertCode.circleRep (a j),
    fun j => HilbertCode.measurable_circleRep_fixed (a j),c,?_,hc⟩
  dsimp only
  simp only [hv]
  have hq : HilbertCode.IsUnimodular (HilbertCode.encode (u p i) v) := by
    rw [←hv]
    exact (ha.2.1 i).2
  exact (HilbertCode.decode_encode (u p i) v).symm.trans
    (HilbertCode.circleLp_circleRep (HilbertCode.encode (u p i) v) hq).symm

variable [StandardBorelSpace P] [StandardBorelSpace U]

lemma exactCodeSpan_sections (hu : Measurable u) (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) (i : I) :
    ∃ s : ℕ → ∀ p, Lp ℂ 2 (κ (u p i)), (∀ n, MeasurableSection (s n)) ∧
      ∀ p, exactCodeSpan κ Λ u p i =
        (Submodule.span ℂ (Set.range (fun n => s n p))).topologicalClosure := by
  obtain ⟨D,a,_,ha,hbase,hmem,hzero,hcover⟩ := exactCode_sections κ Λ u hu hk hm hind
  let s : ℕ → ∀ p, Lp ℂ 2 (κ (u p i)) := fun n p =>
    HilbertCode.atBase (a n p i) (u p i) (hbase n p i)
  have hs (n p) : HilbertCode.encode (u p i) (s n p) = a n p i := HilbertCode.encode_atBase _ _ _
  refine ⟨s,?_,?_⟩
  · intro n
    change Measurable (fun p => HilbertCode.encode (u p i) (s n p))
    simp only [hs]
    exact (measurable_pi_apply i).comp (ha n)
  · intro p
    apply le_antisymm
    · apply Submodule.topologicalClosure_mono
      apply Submodule.span_le.mpr
      rintro v ⟨b,hb,hv⟩
      obtain ⟨n,_,hn⟩ := hcover (p,b) hb
      have he : s n p = v := by
        apply HilbertCode.encode_injective (u p i)
        rw [hs,hn]
        exact hv
      exact Submodule.subset_span ⟨n,he⟩
    · apply Submodule.topologicalClosure_mono
      apply Submodule.span_le.mpr
      rintro _ ⟨n,rfl⟩
      by_cases hp : p ∈ D n
      · exact Submodule.subset_span ⟨a n p,hmem n p hp,(hs n p).symm⟩
      · have he : s n p = 0 := by
          apply HilbertCode.encode_injective (u p i)
          rw [hs,hzero n p hp]
        dsimp only
        rw [he]
        exact Submodule.zero_mem _
end

section
open MeasureTheory ProbabilityTheory Set
variable {P Ω X Y U : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U]
  [retained12 : StandardBorelSpace Ω] [StandardBorelSpace X]
  [StandardBorelSpace Y] [Nonempty Y]
  (Λ : Kernel P Ω) [IsMarkovKernel Λ] (x : Ω → X) (y : Ω → Y)
  (hx : Measurable x) (hy : Measurable y)

omit [StandardBorelSpace Ω] in
include hx hy in
lemma joiningPosterior_conditional (p : P) :
    HasCondDistrib y x ((joiningPosterior Λ x y).sectR p) (Λ p) := by
  let K := Λ.map (fun ω => (x ω,y ω))
  let : IsMarkovKernel K := Kernel.IsMarkovKernel.map _ (hx.prodMk hy)
  have h := congrArg (fun K : Kernel P (X × Y) => K p) (Kernel.disintegrate K K.condKernel)
  rw [Kernel.compProd_apply_eq_compProd_sectR,Kernel.fst_apply,Kernel.map_apply _ (hx.prodMk hy)] at h
  refine ⟨(hx.prodMk hy).aemeasurable,?_⟩
  rw [Measure.map_map measurable_fst (hx.prodMk hy)] at h
  exact h.symm

variable (κ : Kernel U X) [IsMarkovKernel κ] (u : P → U)
  (f : Y → ℂ) (hf : Measurable f) (B : ℝ) (hB : ∀ z, ‖f z‖ ≤ B)

include retained12 in
lemma measurableSection_posteriorVector (hu : Measurable u) :
    MeasurableSection (posteriorVector Λ x y κ u f hf B hB) := by
  let _ := retained12
  exact measurable_hilbert_encode u hu _ (fun pa => ∫ z, f z ∂joiningPosterior Λ x y pa)
    (hf.stronglyMeasurable.integral_kernel (κ := joiningPosterior Λ x y)).measurable
    (fun p => (posterior_memLp Λ x y κ u f hf B hB p).coeFn_toLp)

lemma posteriorVector_eq_operator (p : P)
    (hxm : MeasurePreserving x (Λ p) (κ (u p))) :
    posteriorVector Λ x y κ u f hf B hB p =
      JoiningOperator.operator hxm (MeasurePreserving.mk hy rfl)
        ((MemLp.of_bound hf.aestronglyMeasurable B
          (Filter.Eventually.of_forall hB) : MemLp f 2 ((Λ p).map y)).toLp f) := by
  let g := (MemLp.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall hB) : MemLp f 2 ((Λ p).map y)).toLp f
  have he : (fun ω => g (y ω)) =ᵐ[Λ p] (fun ω => f (y ω)) :=
    (MeasurePreserving.mk hy rfl).quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp _)
  have hl : Integrable (fun ω => f (y ω)) (Λ p) :=
    (MemLp.of_bound (hf.comp hy).aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun ω => hB (y ω))) : MemLp (fun ω => f (y ω)) 2 (Λ p)).integrable (by norm_num)
  have hop := JoiningOperator.operator_ae_eq_condExp hxm (MeasurePreserving.mk hy rfl) g
  have hce := JoiningOperator.condExp_of_kernel hxm.measurable (joiningPosterior_conditional Λ x y hxm.measurable hy p)
    f hf.stronglyMeasurable hl
  have hop' : (fun ω => JoiningOperator.operator hxm (MeasurePreserving.mk hy rfl) g (x ω)) =ᵐ[Λ p]
      (fun ω => ∫ z, f z ∂joiningPosterior Λ x y (p,x ω)) :=
    hop.trans ((condExp_congr_ae he).trans hce)
  have hh : ∀ᵐ z ∂(Λ p).map x, posteriorVector Λ x y κ u f hf B hB p z =
      JoiningOperator.operator hxm (MeasurePreserving.mk hy rfl) g z := by
    apply ae_map_descent _ hxm.measurable
    filter_upwards [hxm.quasiMeasurePreserving.ae_eq_comp
      (posterior_memLp Λ x y κ u f hf B hB p).coeFn_toLp,hop'] with ω hv ho
    exact hv.trans ho.symm
  rw [hxm.map_eq] at hh
  exact Lp.ext hh
end

section
open MeasureTheory ProbabilityTheory Set
variable {Y : Type*} [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
variable {P Ω X U : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
  [MeasurableSpace X] [MeasurableSpace U] [StandardBorelSpace Ω] [StandardBorelSpace X]
  [StandardBorelSpace Y] [Nonempty Y]
  (Λ : Kernel P Ω) [IsMarkovKernel Λ] (x : Ω → X) (y : Ω → Y)
  (κ : Kernel U X) [IsMarkovKernel κ] (u : P → U)

lemma measurableSection_posteriorTest (hu : Measurable u) (n : ℕ) :
    MeasurableSection (posteriorTest Λ x y κ u n) :=
  measurableSection_posteriorVector Λ x y κ u _ (hilbertTestFunction_measurable _)
    (hilbertTestFunction_bounded (hilbertTestKeys n)).choose
    (hilbertTestFunction_bounded (hilbertTestKeys n)).choose_spec hu

lemma posteriorTest_eq_operator (hy : Measurable y) (p : P)
    (hxm : MeasurePreserving x (Λ p) (κ (u p))) (n : ℕ) :
    posteriorTest Λ x y κ u n p =
      JoiningOperator.operator hxm (MeasurePreserving.mk hy rfl) (hilbertTests ((Λ p).map y) n) := by
  rw [posteriorTest,posteriorVector_eq_operator Λ x y hy κ u _ _ _ _ p hxm]
  congr 1
  apply Lp.ext
  exact (MemLp.coeFn_toLp _).trans (hilbertTestVector_coe _ _).symm

lemma operator_range_le_iff_tests {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (L : A →L[ℂ] B)
    (v : ℕ → A) (hv : DenseRange v) (S : Submodule ℂ B) (hS : IsClosed (S : Set B)) :
    (LinearMap.range L.toLinearMap).topologicalClosure ≤ S ↔ ∀ n, L (v n) ∈ S := by
  constructor
  · intro h n
    exact h (Submodule.le_topologicalClosure _ ⟨v n,rfl⟩)
  · intro h
    apply Submodule.topologicalClosure_minimal _ _ hS
    rintro _ ⟨a,rfl⟩
    exact hv.induction_on a (hS.preimage L.continuous) h
end

section
open MeasureTheory ProbabilityTheory
variable {Ω S Z : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace Z]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Ω → S} {z : Ω → Z}
  {κ : Kernel S Z} [IsSFiniteKernel κ]
lemma conditional_ae_lift (hs : Measurable s) (hz : Measurable z)
    (hκ : HasCondDistrib z s κ μ) {P : Z → Prop} (hPm : MeasurableSet {z | P z})
    (hP : ∀ᵐ a ∂μ.map s, ∀ᵐ b ∂κ a, P b) : ∀ᵐ ω ∂μ, P (z ω) := by
  have h : ∀ᵐ sb ∂(μ.map s) ⊗ₘ κ, P sb.2 :=
    (Measure.ae_compProd_iff (hPm.preimage measurable_snd)).mpr hP
  rw [←hκ.map_eq] at h
  exact ae_of_ae_map (hs.prodMk hz).aemeasurable h
end

open MeasureTheory Set

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_OrbitCancellation
attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.arrayLaw_probability _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.localLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

namespace ArrayObjects.Object.Rolled

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators


attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma slotExactSpan_closed (i : I) (ν : Measure (Cell M i)) [IsFiniteMeasure ν] (p : Arr I M.U 1) :
    IsClosed (slotExactSpan M i ν p : Set (Lp ℂ 2 ν)) := Submodule.isClosed_topologicalClosure _

lemma slotExactSpan_le_active (i : I) (ν : Measure (Cell M i)) [IsFiniteMeasure ν] (p : Arr I M.U 1)
    (hx : MeasurePreserving (slotCell M i) (M.ownKernel 1 p) ν) :
    slotExactSpan M i ν p ≤ slotActive M i ν p := by
  apply Submodule.topologicalClosure_minimal _ _ (slotActive_closed M i ν p)
  apply Submodule.span_le.mpr
  rintro v ⟨f,hf,d,rfl,a,c,ha,he⟩
  rw [slotActive_eq M i ν p hx]
  apply Submodule.smul_mem
  apply Submodule.le_topologicalClosure
  let g : (↥(({i} : Finset I)ᶜ) → Arr I M.Y 0) → Circle := fun z => c * ∏ j, a j (z j)
  have hg : Measurable g := measurable_const.mul (Finset.measurable_prod _ fun j _ => (ha j).comp (measurable_pi_apply j))
  refine ⟨circleLp ((M.ownKernel 1 p).map (slotRest M i)) g hg,?_⟩
  exact JoiningOperator.circleLp_operator hx (MeasurePreserving.mk (measurable_slotRest M i) rfl) f g hf hg he

lemma slotExactSpan_le_codeSpan (i : I) (p : Arr I M.U 1)
    (hm : ∀ j, MeasurePreserving (fun z : I → Cell M i => z j) (slotTupleKernel M i p)
      (slotLocal M i (tupleParameter M p j))) :
    slotExactSpan M i (slotLocal M i (tupleParameter M p i)) p ≤
      exactCodeSpan (slotLocal M i) (slotTupleKernel M i) (tupleParameter M) p i := by
  apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
  apply Submodule.span_le.mpr
  rintro v ⟨f,hf,d,rfl,a,c,ha,he⟩
  let b : ↥(({i} : Finset I)ᶜ) → Cell M i → Circle := fun j z => a j (unpadCell M i z)
  have hb (j) : Measurable (b j) := (ha j).comp (measurable_unpadCell M i)
  have hc : ∀ᵐ z ∂slotTupleKernel M i p, ∏ j, circleComplete i f b j (z j) = c := by
    rw [slotTupleKernel,Kernel.map_apply _ (measurable_slotTuple M i)]
    apply ae_map_descent _ (measurable_slotTuple M i)
    filter_upwards [he] with y hy
    apply circleComplete_prod i f b _ c
    exact hy
  have hv := exactCircle_mem_codeSpan (slotLocal M i) (slotTupleKernel M i) (tupleParameter M) p i hm
    (circleComplete i f b) (measurable_circleComplete i f b hf hb) c hc d
  change d • circleLp (slotLocal M i (tupleParameter M p i)) f hf ∈
    exactCodeSpan (slotLocal M i) (slotTupleKernel M i) (tupleParameter M) p i
  simpa only [circleComplete_self] using hv

lemma codeSpan_le_slotExactSpan (i : I) (p : Arr I M.U 1)
    (hm : ∀ j, MeasurePreserving (fun z : I → Cell M i => z j) (slotTupleKernel M i p)
      (slotLocal M i (tupleParameter M p j))) :
    exactCodeSpan (slotLocal M i) (slotTupleKernel M i) (tupleParameter M) p i ≤
      slotExactSpan M i (slotLocal M i (tupleParameter M p i)) p := by
  apply Submodule.topologicalClosure_minimal _ _ (slotExactSpan_closed M i _ p)
  apply Submodule.span_le.mpr
  intro v hv
  obtain ⟨f,hf,c,hv,he⟩ := exactVector_circle_tuple (slotLocal M i) (slotTupleKernel M i)
    (tupleParameter M) p i hm hv
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  refine ⟨f i,hf i,1,?_,(fun j y => (f j (padCell M i y))⁻¹),c,?_,?_⟩
  · simpa only [one_smul] using hv
  · intro j
    exact ((hf j).comp (measurable_padCell M i)).inv
  · have hmap : MeasurePreserving (slotTuple M i) (M.ownKernel 1 p) (slotTupleKernel M i p) :=
      ⟨measurable_slotTuple M i,(Kernel.map_apply _ (measurable_slotTuple M i) _).symm⟩
    filter_upwards [hmap.quasiMeasurePreserving.ae he] with y hy
    exact prod_equation_solve i _ c hy

lemma slotExactSpan_eq_codeSpan (i : I) (p : Arr I M.U 1)
    (hm : ∀ j, MeasurePreserving (fun z : I → Cell M i => z j) (slotTupleKernel M i p)
      (slotLocal M i (tupleParameter M p j))) :
    slotExactSpan M i (slotLocal M i (tupleParameter M p i)) p =
      exactCodeSpan (slotLocal M i) (slotTupleKernel M i) (tupleParameter M) p i :=
  le_antisymm (slotExactSpan_le_codeSpan M i p hm) (codeSpan_le_slotExactSpan M i p hm)
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory Set
variable {P U Y I Ω Z : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U] [MeasurableSpace Y] [StandardBorelSpace Y]
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U) (hu : Measurable u)
  (L : Kernel P Ω) [IsMarkovKernel L] (x : Ω → Y) (z : Ω → Z)

include hu in
lemma measurableSet_code_tests (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) (i : I) :
    MeasurableSet {p | ∀ n, posteriorTest L x z κ (fun p => u p i) n p ∈ exactCodeSpan κ Λ u p i} := by
  obtain ⟨s,hs,he⟩ := exactCodeSpan_sections κ Λ u hu hk hm hind i
  have hv (n) := measurableSection_posteriorTest L x z κ (fun p => u p i)
    ((measurable_pi_apply i).comp hu) n
  simp only [he,Set.ofPred_forall]
  exact MeasurableSet.iInter fun n =>
    measurableSet_section_mem_span ((measurable_pi_apply i).comp hu) hs (hv n)

omit [StandardBorelSpace P] [StandardBorelSpace U] [DecidableEq I] [IsMarkovKernel Λ] in
lemma code_tests_iff_range (hz : Measurable z) (p : P) (i : I)
    (hx : MeasurePreserving x (L p) (κ (u p i))) :
    (∀ n, posteriorTest L x z κ (fun p => u p i) n p ∈ exactCodeSpan κ Λ u p i) ↔
      (LinearMap.range (JoiningOperator.operator hx (MeasurePreserving.mk hz rfl)).toLinearMap).topologicalClosure ≤
        exactCodeSpan κ Λ u p i := by
  simp only [posteriorTest_eq_operator L x z κ (fun p => u p i) hz p hx]
  exact (operator_range_le_iff_tests _ _ (hilbertTests_dense _) _
    (Submodule.isClosed_topologicalClosure _)).symm
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma slot_global_exactness (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (i : I) (s : ComplementSplit ({i} : Finset I)) :
    ∀ᵐ p ∂M.parameterLaw 1, slotActive M i (slotLocal M i (tupleParameter M p i)) p =
      slotExactSpan M i (slotLocal M i (tupleParameter M p i)) p := by
  have hI : 2 ≤ Fintype.card I := by omega
  obtain ⟨L,hL,hLe,hm,hi⟩ := exists_good_tuple_kernel (slotLocal M i) (slotTupleKernel M i)
    (tupleParameter M) (measurable_tupleParameter M) (M.parameterLaw 1)
    (slotTuple_marginal M hI i) (slotTuple_proper M i)
  let : IsMarkovKernel L := hL
  let E := {p | ∀ n, posteriorTest (M.ownKernel 1) (slotCell M i) (slotRest M i)
    (slotLocal M i) (fun p => tupleParameter M p i) n p ∈
      exactCodeSpan (slotLocal M i) L (tupleParameter M) p i}
  have hEm : MeasurableSet E := measurableSet_code_tests (slotLocal M i) L (tupleParameter M)
    (measurable_tupleParameter M) (M.ownKernel 1) (slotCell M i) (slotRest M i) hk hm hi i
  have hκ : HasCondDistrib (id : Arr I M.U 1 → Arr I M.U 1) (plane 0 0 i)
      (M.parameterCoordinateKernel i) (M.parameterLaw 1) :=
    ⟨((measurable_plane _ _ _).prodMk measurable_id).aemeasurable,
      (compProd_map_condDistrib measurable_id.aemeasurable).symm⟩
  have hgood : ∀ᵐ p ∂M.parameterLaw 1,
      L p = slotTupleKernel M i p ∧
      (∀ j, MeasurePreserving (fun z : I → Cell M i => z j) (slotTupleKernel M i p)
        (slotLocal M i (tupleParameter M p j))) ∧
      MeasurePreserving (slotCell M i) (M.ownKernel 1 p)
        (slotLocal M i (tupleParameter M p i)) :=
    hLe.and ((slotTuple_marginal M hI i).and (slotCell_marginal M hI i))
  have hcond := conditional_ae_descent (κ := M.parameterCoordinateKernel i)
    (P := fun u p => plane 0 0 i p = u ∧ L p = slotTupleKernel M i p ∧
      (∀ j, MeasurePreserving (fun z : I → Cell M i => z j) (slotTupleKernel M i p)
        (slotLocal M i (tupleParameter M p j))) ∧
      MeasurePreserving (slotCell M i) (M.ownKernel 1 p)
        (slotLocal M i (tupleParameter M p i)))
    (measurable_plane 0 0 i) measurable_id hκ
    (hgood.mono fun p hp => ⟨rfl,hp⟩)
  rw [M.parameterLaw_consistent 0 0 i] at hcond
  have hE : ∀ᵐ p ∂M.parameterLaw 1, p ∈ E := by
    apply conditional_ae_lift (κ := M.parameterCoordinateKernel i) (measurable_plane 0 0 i) measurable_id hκ hEm
    rw [M.parameterLaw_consistent 0 0 i]
    filter_upwards [slot_conditional_exactness M hM hI i s,hcond] with u hu hg
    filter_upwards [hu,hg] with p hp hg
    rcases hg with ⟨hu,heq,hpm,hxm⟩
    subst u
    apply (code_tests_iff_range (slotLocal M i) L (tupleParameter M) (M.ownKernel 1)
      (slotCell M i) (slotRest M i) (measurable_slotRest M i) p i hxm).mpr
    rw [←slotActive_eq M i _ p hxm]
    change slotActive M i (slotLocal M i (tupleParameter M p i)) p ≤ _ at hp
    rw [exactCodeSpan_congr_kernel (slotLocal M i) L (tupleParameter M) (slotTupleKernel M i) p i heq,
      ←slotExactSpan_eq_codeSpan M i p hpm]
    exact hp
  filter_upwards [hE,hgood] with p hp hg
  apply le_antisymm _ (slotExactSpan_le_active M i _ p hg.2.2)
  have hr := (code_tests_iff_range (slotLocal M i) L (tupleParameter M) (M.ownKernel 1)
    (slotCell M i) (slotRest M i) (measurable_slotRest M i) p i hg.2.2).mp hp
  rw [←slotActive_eq M i _ p hg.2.2,
    exactCodeSpan_congr_kernel (slotLocal M i) L (tupleParameter M) (slotTupleKernel M i) p i hg.1,
    ←slotExactSpan_eq_codeSpan M i p hg.2.1] at hr
  exact hr
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] (κ : Kernel U Y) [IsMarkovKernel κ]

omit [MeasurableSpace.CountablyGenerated Y] in
lemma norm_integral_mul_conj_of_phase {μ : Measure Y} (f g h : Y → ℂ) (c : ℂ)
    (hc : ‖c‖ = 1) (he : g =ᵐ[μ] fun y => c * h y) :
    ‖∫ y, f y * conj (g y) ∂μ‖ = ‖∫ y, f y * conj (h y) ∂μ‖ := by
  have ht : (fun y => f y * conj (g y)) =ᵐ[μ]
      fun y => conj c * (f y * conj (h y)) := he.mono fun y hy => by
    dsimp only at hy ⊢
    rw [hy,map_mul]; ring
  rw [integral_congr_ae ht,integral_const_mul,norm_mul,Complex.norm_conj,hc,one_mul]

lemma absoluteCoefficient_encode_smul (f : Y → ℂ) (a : U)
    (g : Y → Circle) (hg : Measurable g) (d : ℂ) (hd : ‖d‖ = 1) :
    absoluteCoefficient κ f (a,HilbertCode.encode a (d • circleLp (κ a) g hg)) =
      ‖∫ y, f y * conj (g y : ℂ) ∂κ a‖ := by
  let q := HilbertCode.encode a (d • circleLp (κ a) g hg)
  have hr : (fun y => HilbertCode.representative (q,y)) =ᵐ[κ a]
      (fun y => d * (g y : ℂ)) := by
    have h := HilbertCode.representative_eq_decode q
    change (fun y => HilbertCode.representative (q,y)) =ᵐ[κ a]
      (HilbertCode.decode (HilbertCode.encode a (d • circleLp (κ a) g hg)) : Y → ℂ) at h
    rw [HilbertCode.decode_encode] at h
    filter_upwards [h,Lp.coeFn_smul d (circleLp (κ a) g hg),circleLp_coe (κ a) g hg]
      with y h1 h2 h3
    exact h1.trans (h2.trans (congrArg (d * ·) h3))
  have hu : q.IsUnimodular := hr.mono fun y hy => by
    dsimp only at hy
    rw [hy,norm_mul,hd,Circle.norm_coe,mul_one]
  exact norm_integral_mul_conj_of_phase _ _ _ d hd ((HilbertCode.circleRep_ae q hu).trans hr)

omit [MeasurableSpace.CountablyGenerated Y] in
lemma inner_circle_toLp {ν : Measure Y} [IsFiniteMeasure ν]
    (f : Y → ℂ) (hf : MemLp f 2 ν) (g : Y → Circle) (hg : Measurable g) :
    inner ℂ (circleLp ν g hg) (hf.toLp f) = ∫ y, f y * conj (g y : ℂ) ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [circleLp_coe ν g hg,hf.coeFn_toLp] with y h1 h2
  rw [h1,h2]
  rfl
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ComplexConjugate InnerProductSpace
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

omit [DecidableEq I] in
lemma raw_exact_coefficient_zero (p : Arr I M.U 1) (i : I)
    (hm : ∀ j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (f : Arr I M.Y 0 → ℂ)
    (hzero : ∀ q, (p,q) ∈ rawLineGraph M Λ i →
      absoluteCoefficient (M.ownKernel 0) f (tupleParameter M p i,q) = 0)
    (g : I → Arr I M.Y 0 → Circle) (hg : ∀ j, Measurable (g j)) (c : Circle)
    (he : ∀ᵐ y ∂Λ p, ∏ j, g j (y j) = c) :
    ∫ y, f y * conj (g i y : ℂ) ∂M.ownKernel 0 (tupleParameter M p i) = 0 := by
  obtain ⟨a,d,ha,hd⟩ := normalized_exact_codes (M.ownKernel 0) Λ (tupleParameter M)
    p hm g hg c he
  have hz := hzero (a i) ⟨a,ha,rfl⟩
  rw [(hd i).2,absoluteCoefficient_encode_smul _ _ _ _ _ _ (hd i).1] at hz
  exact norm_eq_zero.mp hz

lemma slotExact_coefficient_zero (p : Arr I M.U 1) (i : I)
    (hL : Λ p = rawTupleKernel M p)
    (hm : ∀ j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (f : Arr I M.Y 0 → ℂ)
    (hf : MemLp (f ∘ unpadCell M i) 2 (slotLocal M i (tupleParameter M p i)))
    (hzero : ∀ q, (p,q) ∈ rawLineGraph M Λ i →
      absoluteCoefficient (M.ownKernel 0) f (tupleParameter M p i,q) = 0)
    {v : Lp ℂ 2 (slotLocal M i (tupleParameter M p i))}
    (hv : v ∈ slotExact M i (slotLocal M i (tupleParameter M p i)) p) :
    inner ℂ v (hf.toLp (f ∘ unpadCell M i)) = 0 := by
  obtain ⟨g,hg,d,rfl,a,c,ha,he⟩ := hv
  let b : ↥(({i} : Finset I)ᶜ) → Arr I M.Y 0 → Circle := fun j y => a j y
  have hb (j) : Measurable (b j) := ha j
  let g₀ : Arr I M.Y 0 → Circle := g ∘ padCell M i
  have hg₀ : Measurable g₀ := hg.comp (measurable_padCell M i)
  have ht : ∀ᵐ y ∂Λ p, ∏ j, circleComplete i g₀ b j (y j) = c := by
    rw [hL,rawTupleKernel,Kernel.map_apply _ (measurable_rawTuple M)]
    apply ae_map_descent _ (measurable_rawTuple M)
    filter_upwards [he] with y hy
    apply circleComplete_prod i g₀ b _ c
    exact hy
  have hz := raw_exact_coefficient_zero M Λ p i hm f hzero
    (circleComplete i g₀ b) (measurable_circleComplete i g₀ b hg₀ hb) c ht
  simp only [circleComplete_self] at hz
  rw [inner_smul_left,inner_circle_toLp]
  suffices hh : ∫ y, (f ∘ unpadCell M i) y * conj (g y : ℂ)
      ∂slotLocal M i (tupleParameter M p i) = 0 by rw [hh,mul_zero]
  rw [slotLocal,Kernel.map_apply _ (measurable_padCell M i),integral_map
    (measurable_padCell M i).aemeasurable]
  · exact hz
  · have hmeas : AEStronglyMeasurable (fun y => (f ∘ unpadCell M i) y * conj (g y : ℂ))
        (slotLocal M i (tupleParameter M p i)) := by
      apply hf.aestronglyMeasurable.mul
      exact (continuous_star.measurable.comp (measurable_subtype_coe.comp hg)).aestronglyMeasurable
    simpa only [slotLocal,Kernel.map_apply _ (measurable_padCell M i)] using hmeas

lemma slotActive_orthogonal_of_coefficients_zero (p : Arr I M.U 1) (i : I)
    (hL : Λ p = rawTupleKernel M p)
    (hm : ∀ j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (he : slotActive M i (slotLocal M i (tupleParameter M p i)) p =
      slotExactSpan M i (slotLocal M i (tupleParameter M p i)) p)
    (f : Arr I M.Y 0 → ℂ)
    (hf : MemLp (f ∘ unpadCell M i) 2 (slotLocal M i (tupleParameter M p i)))
    (hzero : ∀ q, (p,q) ∈ rawLineGraph M Λ i →
      absoluteCoefficient (M.ownKernel 0) f (tupleParameter M p i,q) = 0) :
    hf.toLp (f ∘ unpadCell M i) ∈ (slotActive M i (slotLocal M i (tupleParameter M p i)) p)ᗮ := by
  rw [he]
  let K : Submodule ℂ (Lp ℂ 2 (slotLocal M i (tupleParameter M p i))) :=
    (ℂ ∙ hf.toLp (f ∘ unpadCell M i))ᗮ
  have hk : slotExactSpan M i (slotLocal M i (tupleParameter M p i)) p ≤ K := by
    apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_orthogonal _)
    apply Submodule.span_le.mpr
    intro v hv
    apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    exact slotExact_coefficient_zero M Λ p i hL hm f hf hzero hv
  rw [Submodule.mem_orthogonal]
  intro v hv
  exact (Submodule.mem_orthogonal_singleton_iff_inner_left).mp (hk hv)
end ArrayObjects.Object.Rolled

namespace JoiningOperator
open MeasureTheory
open scoped ComplexConjugate InnerProductSpace
variable {Ω Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure Ω} {ν : Measure Y} {η : Measure Z} {x : Ω → Y} {z : Ω → Z}
lemma correlation_zero_of_orthogonal (hx : MeasurePreserving x μ ν) (hz : MeasurePreserving z μ η)
    (f : Y → ℂ) (hf : MemLp f 2 ν) (g : Z → ℂ) (hg : MemLp g 2 η)
    (horth : hf.toLp f ∈ (LinearMap.range (operator hx hz).toLinearMap).topologicalClosureᗮ) :
    ∫ ω, f (x ω) * conj (g (z ω)) ∂μ = 0 := by
  have hv : operator hx hz (hg.toLp g) ∈
      (LinearMap.range (operator hx hz).toLinearMap).topologicalClosure :=
    Submodule.le_topologicalClosure _ ⟨hg.toLp g,rfl⟩
  have he := Submodule.inner_right_of_mem_orthogonal hv horth
  rw [←inner_conj_symm,inner_operator,←integral_conj] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [hx.quasiMeasurePreserving.ae hf.coeFn_toLp,
    hz.quasiMeasurePreserving.ae hg.coeFn_toLp] with ω h1 h2
  rw [h1,h2]
  simp only [RCLike.inner_apply,starRingEnd_apply,map_mul,star_star]
  ring
end JoiningOperator

namespace ConditionalFibres
open MeasureTheory ProbabilityTheory
variable {Ω U Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U] [MeasurableSpace Y]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {x : Ω → U} {y : Ω → Y}
  {κ : Kernel U Y} [IsMarkovKernel κ]
lemma integral_integral_of_bound (h : HasCondDistrib y x κ μ)
    (f : Y → ℂ) (hf : Measurable f) (C : ℝ) (hb : ∀ y, ‖f y‖ ≤ C) :
    ∫ u, ∫ z, f z ∂κ u ∂μ.map x = ∫ ω, f (y ω) ∂μ := by
  have hi : Integrable (fun p : U × Y => f p.2) (μ.map x ⊗ₘ κ) :=
    Integrable.of_bound (hf.comp measurable_snd).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun p => hb p.2)
  rw [←Measure.integral_compProd hi,←h.map_eq]
  exact integral_map h.aemeasurable (hf.comp measurable_snd).aestronglyMeasurable
end ConditionalFibres

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ComplexConjugate InnerProductSpace
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]

lemma slot_product_zero (p : Arr I M.U 1) (i : I)
    (hL : Λ p = rawTupleKernel M p)
    (hm : ∀ j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hx : MeasurePreserving (slotCell M i) (M.ownKernel 1 p)
      (slotLocal M i (tupleParameter M p i)))
    (he : slotActive M i (slotLocal M i (tupleParameter M p i)) p =
      slotExactSpan M i (slotLocal M i (tupleParameter M p i)) p)
    (f : I → Arr I M.Y 0 → ℂ) (hf : ∀ j, Measurable (f j))
    (hb : ∀ j y, ‖f j y‖ ≤ 1)
    (hzero : ∀ q, (p,q) ∈ rawLineGraph M Λ i →
      absoluteCoefficient (M.ownKernel 0) (f i) (tupleParameter M p i,q) = 0) :
    ∫ y, ∏ j, f j (plane 0 0 j y) ∂M.ownKernel 1 p = 0 := by
  let g : (↥(({i} : Finset I)ᶜ) → Arr I M.Y 0) → ℂ :=
    fun z => conj (∏ j : ↥(({i} : Finset I)ᶜ), f j (z j))
  have hgm : Measurable g := continuous_star.measurable.comp
    (Finset.measurable_prod _ fun j _ => (hf j).comp (measurable_pi_apply j))
  have hgb (z) : ‖g z‖ ≤ 1 := by
    dsimp [g]
    rw [Complex.norm_conj, norm_prod]
    exact Finset.prod_le_one (fun j _ => norm_nonneg _) (fun j _ => hb j _)
  let hfi : MemLp (f i ∘ unpadCell M i) 2 (slotLocal M i (tupleParameter M p i)) :=
    MemLp.of_bound ((hf i).comp (measurable_unpadCell M i)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun y => hb i _)
  have ho := slotActive_orthogonal_of_coefficients_zero M Λ p i hL hm he (f i) hfi hzero
  rw [slotActive_eq M i _ p hx] at ho
  have hz := JoiningOperator.correlation_zero_of_orthogonal hx
    (MeasurePreserving.mk (measurable_slotRest M i) rfl) (f i ∘ unpadCell M i) hfi g
    (MemLp.of_bound hgm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hgb)) ho
  convert hz using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp [g,slotCell,slotRest,unpadCell,padCell]
  rw [Complex.conj_conj]
  rw [Fintype.prod_eq_mul_prod_compl i]
  congr 1
  exact (Finset.prod_attach _ (fun j : I => f j (plane 0 0 j y))).symm

lemma raw_correlation_forces_coefficient_oai (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ᵐ p ∂M.parameterLaw 1, ∀ j, {q | (p,q) ∈ rawLineGraph M Λ j} =
      {q | (tupleParameter M p j,q) ∈ S})
    (i : I) (f : I → Arr I M.Y 0 → ℂ) (hf : ∀ j, Measurable (f j))
    (hb : ∀ j y, ‖f j y‖ ≤ 1)
    (hpos : (∫ y, ∏ j, f j (plane 0 0 j y) ∂M.law 1) ≠ 0) :
    ¬ ∀ᵐ a ∂M.parameterLaw 0, ∀ q, (a,q) ∈ S →
      absoluteCoefficient (M.ownKernel 0) (f i) (a,q) = 0 := by
  intro hz
  have hpa : MeasurePreserving (fun p => tupleParameter M p i)
      (M.parameterLaw 1) (M.parameterLaw 0) :=
    ⟨measurable_plane 0 0 i,M.parameterLaw_consistent 0 0 i⟩
  have hzero : ∀ᵐ p ∂M.parameterLaw 1,
      (∫ y, ∏ j, f j (plane 0 0 j y) ∂M.ownKernel 1 p) = 0 := by
    filter_upwards [hL,hS,hpa.quasiMeasurePreserving.ae hz,
      slot_global_exactness M hM hk i (singletonSplit hk i),
      slotCell_marginal M (by omega) i] with p hp hs hz he hx
    apply slot_product_zero M Λ p i hp (hm p) hx he f hf hb
    intro q hq
    exact hz q (by change q ∈ {q | (tupleParameter M p i,q) ∈ S}; rw [←hs i]; exact hq)
  apply hpos
  have hpm : Measurable (fun y : Arr I M.Y 1 => ∏ j, f j (plane 0 0 j y)) :=
    Finset.measurable_prod _ fun j _ => (hf j).comp (measurable_plane _ _ _)
  have hpb (y : Arr I M.Y 1) : ‖∏ j, f j (plane 0 0 j y)‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun j _ => norm_nonneg _) (fun j _ => hb j _)
  have ht := ConditionalFibres.integral_integral_of_bound (M.ownKernel_conditional 1) _ hpm 1 hpb
  exact ht.symm.trans (integral_eq_zero_of_ae hzero)
end ArrayObjects.Object.Rolled

end Rokhlin

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_correlation_forces_coefficient_oai.{u} := @OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_correlation_forces_coefficient_oai.{u}
