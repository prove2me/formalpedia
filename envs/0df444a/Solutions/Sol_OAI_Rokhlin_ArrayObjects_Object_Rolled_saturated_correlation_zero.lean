-- Prove2me | solution 1 for OAI.Rokhlin.ArrayObjects.Object.Rolled.saturated_correlation_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:57:23.700242+00:00
-- url     : https://prove2.me/submissions/d66e2dbb-abc7-4b7e-a74e-e2ad9a3a3913
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ3Ro002
import Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_raw_correlation_zero
import Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_raw_row_active_to_column_exact
import Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_raw_row_indicators_equal
import Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_raw_row_line_projection

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

lemma measurableSet_branched_relation [MeasurableEq Z]
    (f : T → P) (g : T → Z) (hg : Measurable g)
    (d : P → Z) (hd : Measurable d) (C : ℕ → Set T)
    (hcover : (⋃ n, C n) = Set.univ)
    (hemb : ∀ n, MeasurableEmbedding (fun x : C n => f x)) :
    MeasurableSet {pz : P × Z | ∃ t, f t = pz.1 ∧ g t = pz.2} := by
  obtain ⟨D,s,hD,hs,_,hhas,hevery⟩ := measurable_branch_sections f g hg d hd C hcover hemb
  have he : {pz : P × Z | ∃ t, f t = pz.1 ∧ g t = pz.2} =
      ⋃ n, {pz : P × Z | pz.1 ∈ D n ∧ s n pz.1 = pz.2} := by
    ext pz
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · rintro ⟨t,hf,hg⟩
      obtain ⟨n,hn,he⟩ := hevery t
      exact ⟨n,hf ▸ hn,by rw [←hf,he,hg]⟩
    · rintro ⟨n,hn,he⟩
      obtain ⟨t,hf,hg⟩ := hhas n pz.1 hn
      exact ⟨t,hf,hg.symm.trans he⟩
  rw [he]
  exact MeasurableSet.iUnion fun n => (hD n).preimage measurable_fst |>.inter
    (measurableSet_eq_fun ((hs n).comp measurable_fst) measurable_snd)
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

lemma measurableSet_exactCodeSlot (hu : Measurable u) (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) (i : I) :
    MeasurableSet {pz : P × HilbertCode κ | ∃ a : I → HilbertCode κ,
      (pz.1,a) ∈ exactCodeSet κ Λ u ∧ a i = pz.2} := by
  obtain ⟨C,_,hcover,_,hemb⟩ := exactCodeTuple_branches κ Λ u hu hk hm hind
  have hd : Measurable (fun p : P => HilbertCode.encode (u p i) (0 : Lp ℂ 2 (κ (u p i)))) :=
    MeasurableSection.zero ((measurable_pi_apply i).comp hu)
  have h := measurableSet_branched_relation
    (fun t : ExactCodeTuple κ Λ u => t.1.1) (fun t : ExactCodeTuple κ Λ u => t.1.2 i)
    ((measurable_pi_apply i).comp measurable_subtype_coe.snd) _ hd C hcover hemb
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext pz
  constructor
  · rintro ⟨a,ha,he⟩
    exact ⟨⟨(pz.1,a),ha⟩,rfl,he⟩
  · rintro ⟨t,ht,he⟩
    exact ⟨t.1.2,by rw [←ht]; exact t.property,he⟩
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
lemma measurable_circleRep : Measurable (fun qy : HilbertCode κ × Y => circleRep qy.1 qy.2) :=
  measurable_circleOfValue.comp measurable_representative
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
attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.columnGroupKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.columnPairKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunArrαYOfNatNatComplexMemAddSubgroupLpENNRealSubmoduleRawSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunCellComplexMemAddSubgroupLpOfNatENNRealSubmoduleSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleColumnActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleCommonActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleRowActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatCellSlotLocal _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallCellSlotTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallYRawTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYColumnCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYRowCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.rowPairKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.splitRowKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Saturating.instNonemptyDataKind _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.arrayLaw_probability _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.localLaw_probability _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
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

namespace FiniteKernel

variable {ι X : Type*} {Y : ι → Type*}
  [Fintype ι] [MeasurableSpace X] [∀ i, MeasurableSpace (Y i)]

theorem map_pi {Z : ι → Type*} [∀ i, MeasurableSpace (Z i)]
    (κ : ∀ i, Kernel X (Y i)) [∀ i, IsMarkovKernel (κ i)]
    (f : ∀ i, Y i → Z i) (hf : ∀ i, Measurable (f i)) :
    letI : ∀ i, IsMarkovKernel ((κ i).map (f i)) :=
      fun i => Kernel.IsMarkovKernel.map (κ i) (hf i)
    (pi κ).map (fun y i => f i (y i)) = pi (fun i => (κ i).map (f i)) := by
  ext x : 1
  rw [Kernel.map_apply _ (by fun_prop)]
  simp only [pi_apply, Kernel.map_apply _ (hf _)]
  exact Measure.pi_map_pi (fun i => (hf i).aemeasurable)

end FiniteKernel

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

namespace ConditionalTransport
variable {Ω Ω' A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

omit [MeasurableSpace Ω] in

theorem comap_le_of_factor {f : Ω → A} {g : Ω → C} {p : C → A}
    (hp : Measurable p) (h : f = p ∘ g) :
    MeasurableSpace.comap f inferInstance ≤ MeasurableSpace.comap g inferInstance := by
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hp.comap_le

end ConditionalTransport

namespace ConditionalScreens
variable {Ω S Z O : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
  [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
  [MeasurableSpace O] [StandardBorelSpace O] [Nonempty O]

theorem reverse_screen {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : Ω → S} {z : Ω → Z} {o : Ω → O}
    (hs : Measurable s) (hz : Measurable z) (ho : Measurable o)
    (f : Z → S) (hf : Measurable f) (g : O → S) (hg : Measurable g)
    (hsz : s = f ∘ z) (hso : s = g ∘ o)
    (κ : Kernel S O) [IsMarkovKernel κ] (l : Kernel S Z) [IsMarkovKernel l]
    (hκ : HasCondDistrib o s κ μ)
    (hl : HasCondDistrib z o (l.comap g hg) μ) :
    HasCondDistrib o z (κ.comap f hf) μ := by
  have hl' : HasCondDistrib z (fun ω => (s ω, o ω)) (l.prodMkRight O) μ := by
    apply ConditionalTransport.recondition ho (hs.prodMk ho) hz hl
    · apply le_antisymm
      · exact ConditionalTransport.comap_le_of_factor measurable_snd rfl
      · apply ConditionalTransport.comap_le_of_factor (hg.prodMk measurable_id)
        simpa only [Function.comp_def, id_eq] using congrArg (fun v => fun ω => (v ω, o ω)) hso
    · filter_upwards [] with ω
      change l (g (o ω)) = l (s ω)
      rw [hso]; rfl
  have hh := screening hκ l hl'
  apply ConditionalTransport.recondition (hs.prodMk hz) hz ho hh
  · apply le_antisymm
    · apply ConditionalTransport.comap_le_of_factor (hf.prodMk measurable_id)
      simpa only [Function.comp_def, id_eq] using congrArg (fun v => fun ω => (v ω, z ω)) hsz
    · exact ConditionalTransport.comap_le_of_factor measurable_snd rfl
  · filter_upwards [] with ω
    change κ (s ω) = κ (f (z ω))
    rw [hsz]; rfl

end ConditionalScreens

namespace FiniteKernel
variable {ι : Type*} [Fintype ι] {Y S : ι → Type*}
  [∀ i, MeasurableSpace (Y i)] [∀ i, StandardBorelSpace (Y i)] [∀ i, Nonempty (Y i)]
  [∀ i, MeasurableSpace (S i)]

theorem independent_observation (μ : ∀ i, Measure (Y i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : ∀ i, Y i → S i)
    (hf : ∀ i, Measurable (f i)) :
    HasCondDistrib (id : (∀ i, Y i) → (∀ i, Y i)) (fun y i => f i (y i))
      (pi (fun i => (condDistrib id (f i) (μ i)).comap (Function.eval i)
        (measurable_pi_apply i))) (Measure.pi μ) := by
  refine ⟨((Measurable.of_eval (fun i => (hf i).comp (measurable_pi_apply i))).prodMk
    measurable_id).aemeasurable, ?_⟩
  let (i : ι) : IsProbabilityMeasure ((μ i).map (f i)) :=
    (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (hf i).aemeasurable
  apply (zipEquiv S Y).measurableEmbedding.map_injective
  rw [Measure.pi_map_pi (fun i => (hf i).aemeasurable), compProd_pi]
  rw [Measure.map_map (zipEquiv S Y).measurable (by fun_prop)]
  change (Measure.pi μ).map (fun y i => (f i (y i), y i)) =
    Measure.pi (fun i => (μ i).map (f i) ⊗ₘ condDistrib id (f i) (μ i))
  calc
    _ = Measure.pi (fun i => (μ i).map (fun y => (f i y, y))) :=
      Measure.pi_map_pi (fun i => ((hf i).prodMk measurable_id).aemeasurable)
    _ = _ := ?_
  congr 1
  funext i
  exact (compProd_map_condDistrib (μ := μ i) (X := f i)
    (Y := id) measurable_id.aemeasurable).symm

end FiniteKernel

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma outside_row_screen (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (a j₀ : I) (n : ℕ) :
    HasCondDistrib (plane (n + 1) 0 a) (planes (n + 1) (Outside j₀))
      ((condDistrib id (planes n (Outside j₀)) (M.law (n + 1))).comap
        (fun o : Outside j₀ → Arr I M.Y (n + 1) => fun j => plane n 0 a (o j))
        (Measurable.of_eval (fun j => (measurable_plane _ _ _).comp (measurable_pi_apply j))))
      (M.law (n + 2)) := by
  have hR : (∅ : Finset I).card + 2 ≤ Fintype.card I := by simpa using hI
  let N := object M hM ∅ hR a (Finset.notMem_empty a)
  let e := objectExtension M hM ∅ hR a (Finset.notMem_empty a)
  let p : (Outside j₀ → Arr I (State M) n) → (Outside j₀ → Arr I M.Y n) :=
    fun o j => amap (Function.eval a) n (o j)
  have hpm : Measurable p := Measurable.of_eval (fun j =>
    (measurable_amap (measurable_pi_apply a) n).comp (measurable_pi_apply j))
  have hs := hM.hasCondDistrib e n (.outside j₀)
    (planes n (Outside j₀)) (planes (Y := State M) n (Outside j₀))
    (id : Arr I M.Y (n + 1) → Arr I M.Y (n + 1)) p
    (measurable_planes _ _) (measurable_planes _ _) measurable_id hpm rfl rfl rfl
  have hp := ConditionalTransport.pullback
    (show MeasurePreserving (roll (Y := M.Y) (n + 1)) (M.law (n + 2)) (N.law (n + 1)) from
      ⟨(roll (n + 1)).measurable, rfl⟩) (measurable_planes _ _) hs
  let E : (Outside j₀ → Arr I (State M) n) ≃ᵐ (Outside j₀ → Arr I M.Y (n + 1)) :=
    MeasurableEquiv.piCongrRight (fun _ => (roll n).symm)
  change HasCondDistrib ((id ∘ amap (Function.eval a) (n + 1)) ∘ roll (n + 1))
    (planes (Y := State M) n (Outside j₀) ∘ roll (n + 1))
    ((condDistrib (id : Arr I M.Y (n + 1) → Arr I M.Y (n + 1))
      (planes n (Outside j₀)) (M.law (n + 1))).comap p hpm) (M.law (n + 2)) at hp
  have h := hp.measurableEquiv_comp_right E
  change HasCondDistrib ((id ∘ amap (Function.eval a) (n + 1)) ∘ roll (n + 1))
    (E ∘ planes n (Outside j₀) ∘ roll (n + 1))
    (((condDistrib id (planes n (Outside j₀)) (M.law (n + 1))).comap p hpm).comap
      E.symm E.symm.measurable) (M.law (n + 2)) at h
  have he : E ∘ planes n (Outside j₀) ∘ roll (n + 1) = planes (n + 1) (Outside j₀) := by
    rw [planes_roll]
    funext y j
    change (roll n).symm (roll n (planes (n + 1) (Outside j₀) y j)) = _
    exact (roll n).symm_apply_apply _
  rw [Function.id_comp, select_roll, he] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext o : 1
  change condDistrib id (planes n (Outside j₀)) (M.law (n + 1))
    (fun j => plane n 0 a (o j)) =
    condDistrib id (planes n (Outside j₀)) (M.law (n + 1)) (p (E.symm o))
  congr 1
  funext j
  exact (congrFun (select_roll n a) (o j)).symm

omit [DecidableEq I] in

lemma plane_first_last (n : ℕ) (a j : I) :
    plane (Y := M.Y) n 0 a ∘ plane (n + 1) (Fin.last (n + 1)) j =
      plane n (Fin.last n) j ∘ plane (n + 1) 0 a := by
  funext y v
  change y ((Fin.last (n + 1)).insertNth j ((0 : Fin (n + 1)).insertNth a v)) =
    y ((0 : Fin (n + 2)).insertNth a ((Fin.last n).insertNth j v))
  simp only [Fin.insertNth_last', Fin.insertNth_zero']
  rw [cons_snoc]

theorem columns_given_row (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (a j₀ : I) (n : ℕ) :
    HasCondDistrib (planes (n + 1) (Outside j₀)) (plane (n + 1) 0 a)
      (FiniteKernel.pi (fun j : Outside j₀ =>
        (condDistrib id (plane n 0 a) (M.law (n + 1))).comap
          (plane n (Fin.last n) j) (measurable_plane _ _ _))) (M.law (n + 2)) := by
  let f : Arr I M.Y (n + 1) → Outside j₀ → Arr I M.Y n := planes n (Outside j₀)
  let g : (Outside j₀ → Arr I M.Y (n + 1)) → Outside j₀ → Arr I M.Y n :=
    fun o j => plane n 0 a (o j)
  have hf : Measurable f := measurable_planes _ _
  have hg : Measurable g := Measurable.of_eval (fun j =>
    (measurable_plane _ _ _).comp (measurable_pi_apply j))
  let κ := FiniteKernel.pi (fun _j : Outside j₀ =>
    (condDistrib (id : Arr I M.Y (n + 1) → Arr I M.Y (n + 1))
      (plane n 0 a) (M.law (n + 1))).comap
        (Function.eval _j) (measurable_pi_apply _j))
  let l := condDistrib (id : Arr I M.Y (n + 1) → Arr I M.Y (n + 1)) f (M.law (n + 1))
  have hJ : Outside j₀ ≠ Finset.univ := by
    intro he
    have hj : j₀ ∈ Outside j₀ := he ▸ Finset.mem_univ j₀
    simp only [Outside, Finset.mem_erase, ne_eq, not_true_eq_false, false_and] at hj
  have ho : MeasurePreserving (planes (n + 1) (Outside j₀)) (M.law (n + 2))
      (Measure.pi (fun _ : Outside j₀ => M.law (n + 1))) :=
    ⟨measurable_planes _ _, M.proper _ _ hJ⟩
  have hk := ConditionalTransport.pullback ho hg
    (FiniteKernel.independent_observation (fun _ : Outside j₀ => M.law (n + 1))
      (fun _ => plane n 0 a) (fun _ => measurable_plane _ _ _))
  have hs : g ∘ planes (n + 1) (Outside j₀) = f ∘ plane (n + 1) 0 a := by
    funext y j
    exact congrFun (plane_first_last M n a j) y
  have h := ConditionalScreens.reverse_screen
    (hg.comp (measurable_planes _ _)) (measurable_plane _ _ _) (measurable_planes _ _)
    f hf g hg hs rfl κ l hk (outside_row_screen M hM hI a j₀ n)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext z : 1
  rfl

end ArrayObjects.Object.Rolled

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

omit [DecidableEq I] in

lemma column_parameter_given_cell (hI : 2 ≤ Fintype.card I) (a : I) :
    HasCondDistrib (amap M.par 1) (plane 0 0 a)
      ((M.parameterCoordinateKernel a).comap (amap M.par 0)
        (measurable_amap M.measurable_par 0)) (M.law 1) := by
  have hc : HasCondDistrib (id : Arr I M.U 1 → Arr I M.U 1) (plane 0 0 a)
      (M.parameterCoordinateKernel a) (M.parameterLaw 1) :=
    ⟨((measurable_plane _ _ _).prodMk measurable_id).aemeasurable,
      (compProd_map_condDistrib measurable_id.aemeasurable).symm⟩
  have hq := ConditionalTransport.pullback
    (show MeasurePreserving (amap M.par 1) (M.law 1) (M.parameterLaw 1) from
      ⟨measurable_amap M.measurable_par _, rfl⟩) (measurable_plane _ _ _) hc
  exact ConditionalScreens.reverse_screen
    (s := amap M.par 0 ∘ plane 0 0 a) (z := plane 0 0 a) (o := amap M.par 1)
    ((measurable_amap M.measurable_par 0).comp (measurable_plane _ _ _))
    (measurable_plane _ _ _) (measurable_amap M.measurable_par _)
    (amap M.par 0) (measurable_amap M.measurable_par _) (plane 0 0 a)
    (measurable_plane _ _ _) rfl rfl (M.parameterCoordinateKernel a) (M.ownKernel 0)
    hq (M.plane_conditional hI 0 a)

omit [DecidableEq I] in

lemma shared_parameter_kernel (hI : 2 ≤ Fintype.card I) (a : I) :
    (fun s => (condDistrib (id : Arr I M.Y 1 → Arr I M.Y 1) (plane 0 0 a)
      (M.law 1) s).map (amap M.par 1)) =ᵐ[M.law 0]
    fun s => M.parameterCoordinateKernel a (amap M.par 0 s) := by
  let κ := condDistrib (id : Arr I M.Y 1 → Arr I M.Y 1) (plane 0 0 a) (M.law 1)
  have h : HasCondDistrib id (plane 0 0 a) κ (M.law 1) :=
    ⟨((measurable_plane _ _ _).prodMk measurable_id).aemeasurable,
      (compProd_map_condDistrib measurable_id.aemeasurable).symm⟩
  have hm := h.comp_left (measurable_amap M.measurable_par 1)
  have he := Kernel.ae_eq_of_compProd_eq
    (hm.map_eq.symm.trans (M.column_parameter_given_cell hI a).map_eq)
  rw [show (M.law 1).map (plane 0 0 a) = M.law 0 from M.consistent 0 0 a] at he
  exact he.mono (fun s hs => by
    simpa only [Kernel.map_apply _ (measurable_amap M.measurable_par _), Kernel.comap_apply] using hs)

end ArrayObjects.Object

namespace ConditionalTransport
variable {Ω Ω' A B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [MeasurableSpace B]

theorem pushforward {P : Measure Ω} {Q : Measure Ω'} {f : Ω → Ω'}
    {E : Ω' → A} {O : Ω' → B} {κ : Kernel A B}
    (hf : MeasurePreserving f P Q) (hE : Measurable E) (hO : Measurable O)
    (h : HasCondDistrib (O ∘ f) (E ∘ f) κ P) : HasCondDistrib O E κ Q := by
  refine ⟨(hE.prodMk hO).aemeasurable, ?_⟩
  have he : P.map (E ∘ f) = Q.map E := by
    rw [← Measure.map_map hE hf.measurable, hf.map_eq]
  have hj : P.map (fun ω => (E (f ω), O (f ω))) = Q.map (fun ω => (E ω, O ω)) := by
    change P.map ((fun ω => (E ω, O ω)) ∘ f) = _
    rw [← Measure.map_map (hE.prodMk hO) hf.measurable, hf.map_eq]
  rw [← he]
  exact hj.symm.trans h.map_eq
end ConditionalTransport

namespace ArrayObjects.Object.Rolled
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

theorem columns_parameter_given_row (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (a j₀ : I) :
    HasCondDistrib (fun y => fun j : Outside j₀ => amap M.par 1 (planes 1 (Outside j₀) y j))
      (amap M.par 1 ∘ plane 1 0 a)
      (FiniteKernel.pi (fun j : Outside j₀ => (M.parameterCoordinateKernel a).comap
        (plane 0 0 j) (measurable_plane _ _ _))) (M.law 2) := by
  let κ := condDistrib (id : Arr I M.Y 1 → Arr I M.Y 1) (plane 0 0 a) (M.law 1)
  let η := FiniteKernel.pi (fun j : Outside j₀ => (M.parameterCoordinateKernel a).comap
    (plane 0 0 j) (measurable_plane _ _ _))
  have h := (columns_given_row M hM hI a j₀ 0).comp_left
    (Measurable.of_eval (fun j => (measurable_amap M.measurable_par 1).comp
      (measurable_pi_apply j)))
  simp only [Function.comp_def] at h
  rw [FiniteKernel.map_pi _ _ (fun _ => measurable_amap M.measurable_par 1)] at h
  have he : ∀ᵐ z ∂M.law 1, ∀ j : Outside j₀,
      (κ (plane 0 0 j z)).map (amap M.par 1) =
        M.parameterCoordinateKernel a (amap M.par 0 (plane 0 0 j z)) := by
    rw [ae_all_iff]
    intro j
    exact (show MeasurePreserving (plane 0 0 (j : I)) (M.law 1) (M.law 0) from
      ⟨measurable_plane _ _ _, M.consistent 0 0 j⟩).quasiMeasurePreserving.ae_eq_comp
      (M.shared_parameter_kernel hI a)
  have hk : HasCondDistrib
      (fun y => fun j : Outside j₀ => amap M.par 1 (planes 1 (Outside j₀) y j))
      (plane 1 0 a) (η.comap (amap M.par 1) (measurable_amap M.measurable_par 1))
      (M.law 2) := by
    refine ⟨h.aemeasurable, h.map_eq.trans (Measure.compProd_congr ?_)⟩
    rw [M.consistent 1 0 a]
    filter_upwards [he] with z hz
    change Measure.pi (fun j : Outside j₀ =>
      ((κ.comap (plane 0 (Fin.last 0) j) (measurable_plane _ _ _)).map (amap M.par 1)) z) =
      Measure.pi (fun j : Outside j₀ => M.parameterCoordinateKernel a
        (plane 0 0 j (amap M.par 1 z)))
    congr 1
    funext j
    rw [Kernel.map_apply _ (measurable_amap M.measurable_par _), Kernel.comap_apply,
      Fin.last_zero]
    exact hz j
  exact hk.comp_right

theorem parameter_geometry_outside (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (a j₀ : I) :
    HasCondDistrib (planes 1 (Outside j₀)) (plane 1 0 a)
      (FiniteKernel.pi (fun j : Outside j₀ => (M.parameterCoordinateKernel a).comap
        (plane 0 0 j) (measurable_plane _ _ _))) (M.parameterLaw 2) := by
  apply ConditionalTransport.pushforward
    (show MeasurePreserving (amap M.par 2) (M.law 2) (M.parameterLaw 2) from
      ⟨measurable_amap M.measurable_par _, rfl⟩)
    (measurable_plane _ _ _) (measurable_planes _ _)
  exact columns_parameter_given_row M hM hI a j₀

theorem parameter_geometry (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (a : I) (J : Finset I) (hJ : J ≠ Finset.univ) :
    HasCondDistrib (planes 1 J) (plane 1 0 a)
      (FiniteKernel.pi (fun j : J => (M.parameterCoordinateKernel a).comap
        (plane 0 0 j) (measurable_plane _ _ _))) (M.parameterLaw 2) := by
  have hex : ∃ j₀ : I, j₀ ∉ J := by
    by_contra he
    push Not at he
    exact hJ (Finset.eq_univ_iff_forall.mpr he)
  obtain ⟨j₀, hj₀⟩ := hex
  let e : J ↪ Outside j₀ :=
    ⟨fun j => ⟨j, by
      simp only [Outside, Finset.mem_erase, Finset.mem_univ, and_true]
      exact fun he => hj₀ (he ▸ j.property)⟩,
      fun _ _ he => Subtype.ext (congrArg (fun z : Outside j₀ => (z : I)) he)⟩
  have h := (parameter_geometry_outside M hM hI a j₀).comp_left
    (Measurable.of_eval (fun i => measurable_pi_apply (e i)))
  rw [FiniteKernel.pi_precomp] at h
  exact h

end ArrayObjects.Object.Rolled

namespace ConditionalScreens
variable {Ω S Z O : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
  [MeasurableSpace Z] [MeasurableSpace O] [StandardBorelSpace O] [Nonempty O]

theorem joint_of_screen {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : Ω → S} {z : Ω → Z} {o : Ω → O}
    (hs : Measurable s) (hz : Measurable z) (ho : Measurable o)
    (f : Z → S) (hf : Measurable f) (hsz : s = f ∘ z)
    (κ : Kernel S Z) [IsMarkovKernel κ] (l : Kernel S O) [IsMarkovKernel l]
    (hκ : HasCondDistrib z s κ μ)
    (hl : HasCondDistrib o z (l.comap f hf) μ) :
    HasCondDistrib (fun ω => (z ω, o ω)) s (κ ×ₖ l) μ := by
  have hl' : HasCondDistrib o (fun ω => (s ω, z ω)) (l.prodMkRight Z) μ := by
    apply ConditionalTransport.recondition hz (hs.prodMk hz) ho hl
    · apply le_antisymm
      · exact ConditionalTransport.comap_le_of_factor measurable_snd rfl
      · apply ConditionalTransport.comap_le_of_factor (hf.prodMk measurable_id)
        simpa only [Function.comp_def, id_eq] using congrArg (fun v => fun ω => (v ω, z ω)) hsz
    · filter_upwards [] with ω
      change l (f (z ω)) = l (s ω)
      rw [hsz]; rfl
  have h := chain hκ hl'
  rwa [compProd_prodMkRight] at h
end ConditionalScreens

namespace ArrayObjects.Object
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

variable [DecidableEq I]

theorem diagonal_parameter_product (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I) (i : I) :
    HasCondDistrib (fun p => (plane 1 0 i p, plane 1 (Fin.last 1) i p))
      (plane 0 0 i ∘ plane 1 0 i)
      ((M.parameterCoordinateKernel i) ×ₖ (M.parameterCoordinateKernel i))
      (M.parameterLaw 2) := by
  have hproper : ({i} : Finset I) ≠ Finset.univ := by
    intro he
    have hc := congrArg Finset.card he
    simp only [Finset.card_singleton, Finset.card_univ] at hc
    omega
  have hcol := (Rolled.parameter_geometry M hM hI i {i} hproper).comp_left
    (measurable_pi_apply (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset I)))
  rw [FiniteKernel.map_eval] at hcol
  have hc : HasCondDistrib (id : Arr I M.U 1 → Arr I M.U 1) (plane 0 0 i)
      (M.parameterCoordinateKernel i) (M.parameterLaw 1) :=
    ⟨((measurable_plane _ _ _).prodMk measurable_id).aemeasurable,
      (compProd_map_condDistrib measurable_id.aemeasurable).symm⟩
  have hrow := ConditionalTransport.pullback
    (show MeasurePreserving (plane 1 0 i) (M.parameterLaw 2) (M.parameterLaw 1) from
      ⟨measurable_plane _ _ _, M.parameterLaw_consistent 1 0 i⟩)
    (measurable_plane _ _ _) hc
  exact ConditionalScreens.joint_of_screen
    (s := plane 0 0 i ∘ plane 1 0 i) (z := plane 1 0 i) (o := plane 1 (Fin.last 1) i)
    ((measurable_plane _ _ _).comp (measurable_plane _ _ _))
    (measurable_plane _ _ _) (measurable_plane _ _ _)
    (plane 0 0 i) (measurable_plane _ _ _) rfl
    (M.parameterCoordinateKernel i) (M.parameterCoordinateKernel i) hrow hcol

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

section

open MeasureTheory Filter ContinuousLinearMap
open scoped InnerProductSpace Topology

section EssentialKernel
variable {X E H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem essentialKernel.ae_annihilate [SecondCountableTopology E]
    (μ : Measure X) (A : X → E →L[ℂ] H) :
    ∀ᵐ x ∂μ, ∀ v : essentialKernel μ A, A x v = 0 := by
  let K := essentialKernel μ A
  have h (n : ℕ) : ∀ᵐ x ∂μ, A x (TopologicalSpace.denseSeq K n) = 0 :=
    (TopologicalSpace.denseSeq K n).property
  filter_upwards [ae_all_iff.mpr h] with x hx
  have hh : (fun v : K => A x v) = (fun _ : K => (0 : H)) := by
    apply (TopologicalSpace.denseRange_denseSeq K).equalizer
      ((A x).continuous.comp continuous_subtype_val) continuous_const
    funext n
    exact hx n
  intro v
  exact congrFun hh v
end EssentialKernel

section EssentialRange
variable {X E H J : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

lemma essentialRange.ae_range_le [SecondCountableTopology H]
    (μ : Measure X) (F : X → E →L[ℂ] H) :
    ∀ᵐ x ∂μ, LinearMap.range (F x).toLinearMap ≤ essentialRange μ F := by
  filter_upwards [essentialKernel.ae_annihilate μ (fun x => (F x).adjoint)] with x hx
  rintro v ⟨w, rfl⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  intro z hz
  change inner ℂ z (F x w) = 0
  rw [← adjoint_inner_left, hx ⟨z, hz⟩, inner_zero_left]

end EssentialRange

end

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

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
variable {P H : Type*} [MeasurableSpace P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SecondCountableTopology H]

omit [SecondCountableTopology H] in

lemma essential_projection_not_ae_zero (μ : Measure P)
    (V : P → Submodule ℂ H) [∀ p, (V p).HasOrthogonalProjection]
    (v : H) (hv : v ∈ essentialRange μ (fun p => (V p).starProjection)) (hne : v ≠ 0) :
    ¬ ∀ᵐ p ∂μ, (V p).starProjection v = 0 := by
  intro hz
  have hk : v ∈ essentialKernel μ (fun p => (V p).starProjection.adjoint) := by
    change ∀ᵐ p ∂μ, (V p).starProjection.adjoint v = 0
    simpa only [(isSelfAdjoint_starProjection _).adjoint_eq] using hz
  exact hne ((inner_self_eq_zero (𝕜 := ℂ)).mp ((Submodule.mem_orthogonal _ _).mp hv v hk))

lemma active_projection_not_ae_zero (μ : Measure P)
    (V : P → Submodule ℂ H) [∀ p, (V p).HasOrthogonalProjection] :
    ∀ᵐ p ∂μ, ∀ v ∈ V p, v ≠ 0 → ¬ ∀ᵐ q ∂μ, (V q).starProjection v = 0 := by
  filter_upwards [essentialRange.ae_range_le μ (fun p => (V p).starProjection)] with p hp
  intro v hv hne
  exact essential_projection_not_ae_zero μ V v
    (hp ⟨v,(V p).starProjection_eq_self_iff.mpr hv⟩) hne
end

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

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set

section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

omit [DecidableEq I] in
lemma rawTuple_marginal (hI : 2 ≤ Fintype.card I) :
    ∀ᵐ p ∂M.parameterLaw 1, ∀ j,
      MeasurePreserving (fun z : I → Arr I M.Y 0 => z j) (rawTupleKernel M p)
        (M.ownKernel 0 (tupleParameter M p j)) := by
  have h (j : I) := ConditionalFibres.marginal (measurable_plane 0 0 j)
    (M.ownKernel_conditional 1) (M.plane_conditional hI 0 j)
  filter_upwards [ae_all_iff.mpr h] with p hp j
  refine ⟨measurable_pi_apply j,?_⟩
  rw [rawTupleKernel,Kernel.map_apply _ (measurable_rawTuple M),
    Measure.map_map (measurable_pi_apply j) (measurable_rawTuple M)]
  exact (hp j).map_eq

lemma rawTuple_proper :
    ∀ᵐ p ∂M.parameterLaw 1, ∀ j,
      iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
        fun z : I → Arr I M.Y 0 => z t) (rawTupleKernel M p) := by
  filter_upwards [ae_all_iff.mpr (tuple_planes_product M)] with p hp j
  rw [rawTupleKernel,Kernel.map_apply _ (measurable_rawTuple M)]
  apply (iIndepFun_map_iff_measurable (J := ↥(Finset.univ.erase j)) _ _ _
    (fun t => measurable_pi_apply (t : I)) (measurable_rawTuple M)).mpr
  have h := iIndepFun_pi (μ := fun t : (Finset.univ.erase j : Finset I) =>
    M.ownKernel 0 (plane 0 0 t p)) (fun _ : (Finset.univ.erase j : Finset I) =>
    measurable_id.aemeasurable)
  rw [←(hp j).map_eq] at h
  exact (iIndepFun_map_iff_measurable (M.ownKernel 1 p)
    (fun (b : ↥(Finset.univ.erase j : Finset I) → Arr I M.Y 0) t => b t)
    (planes 0 (Finset.univ.erase j)) (fun t => measurable_pi_apply t)
    (measurable_planes 0 _)).mp h

lemma raw_good_tuple_kernel (hI : 2 ≤ Fintype.card I) :
    ∃ Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0), IsMarkovKernel Λ ∧
      Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M ∧
      (∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
        (M.ownKernel 0 (tupleParameter M p j))) ∧
      (∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
        fun y : I → Arr I M.Y 0 => y t) (Λ p)) :=
  exists_good_tuple_kernel (M.ownKernel 0) (rawTupleKernel M) (tupleParameter M)
    (measurable_tupleParameter M) (M.parameterLaw 1) (rawTuple_marginal M hI) (rawTuple_proper M)
end

universe u

end ArrayObjects.Object.Rolled

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
open MeasureTheory ProbabilityTheory
namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma rawSlotActive_eq (i : I) (ν : Measure (Arr I M.Y 0)) (p : Arr I M.U 1)
    (h : MeasurePreserving (plane 0 0 i) (M.ownKernel 1 p) ν) :
    rawSlotActive M i ν p = (LinearMap.range (JoiningOperator.operator h
      (MeasurePreserving.mk (measurable_slotRest M i) rfl)).toLinearMap).topologicalClosure := by
  rw [rawSlotActive,dite_eq_left h]

end ArrayObjects.Object.Rolled
end

section
open MeasureTheory
open scoped BigOperators
variable {I Y : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Y]

lemma prod_complement (i : I) (g : I → Circle) :
    (∏ j, g j) = g i * ∏ j : ↥(({i} : Finset I)ᶜ), g j := by
  rw [Fintype.prod_eq_mul_prod_compl i g,Finset.prod_coe_sort]

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
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace ArrayObjects.Object.Rolled

section
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
lemma raw_tuple_active (i : I) (p : Arr I M.U 1) (ν : Measure (Arr I M.Y 0)) [IsFiniteMeasure ν]
    (hm : MeasurePreserving (plane 0 0 i) (M.ownKernel 1 p) ν)
    (f : I → Arr I M.Y 0 → Circle) (hf : ∀ i, Measurable (f i)) (c : Circle)
    (he : ∀ᵐ y ∂M.ownKernel 1 p, ∏ j, f j (plane 0 0 j y) = c) :
    circleLp ν (f i) (hf i) ∈ rawSlotActive M i ν p := by
  rw [rawSlotActive_eq M i ν p hm]
  apply Submodule.le_topologicalClosure
  let g : (↥(({i} : Finset I)ᶜ) → Arr I M.Y 0) → Circle :=
    fun z => c * ∏ j : ↥(({i} : Finset I)ᶜ), (f j (z j))⁻¹
  have hg : Measurable g := measurable_const.mul (Finset.measurable_prod _ fun j _ =>
    ((hf j).comp (measurable_pi_apply j)).inv)
  refine ⟨circleLp ((M.ownKernel 1 p).map (slotRest M i)) g hg,?_⟩
  apply JoiningOperator.circleLp_operator hm (MeasurePreserving.mk (measurable_slotRest M i) rfl)
    (f i) g (hf i) hg
  exact he.mono fun y hy => prod_equation_solve i (fun j => f j (plane 0 0 j y)) c hy

end

attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u

end ArrayObjects.Object.Rolled
end

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

omit [DecidableEq I] in
lemma canonical_smul_exact_tuple (p : P) (i : I)
    (hm : ∀ j, MeasurePreserving (fun y : I → Y => y j) (Λ p) (κ (u p j)))
    (v : Lp ℂ 2 (κ (u p i))) (hv : RayCanonical (hilbertTests (κ (u p i))) v) (hn : ‖v‖ = 1)
    (f : I → Y → Circle) (hf : ∀ j, Measurable (f j)) (c : Circle) (d : ℂ)
    (he : ∀ᵐ y ∂Λ p, ∏ j, f j (y j) = c)
    (hvd : v = d • circleLp (κ (u p i)) (f i) (hf i)) :
    ∃ a : I → HilbertCode κ, (p,a) ∈ exactCodeSet κ Λ u ∧
      a i = HilbertCode.encode (u p i) v := by
  obtain ⟨a,b,ha,hb⟩ := normalized_exact_codes κ Λ u p hm f hf c he
  have hdn : ‖d‖ = 1 := by
    rw [hvd,norm_smul,circleLp_norm,mul_one] at hn
    exact hn
  let w := b i • circleLp (κ (u p i)) (f i) (hf i)
  have hc : RayCanonical (hilbertTests (κ (u p i))) w := by
    have h := (ha.2.1 i).1
    change HilbertCode.IsCanonical (a i) at h
    rw [(hb i).2] at h
    change RayCanonical (hilbertTests (κ (u p i))) (HilbertCode.decode (HilbertCode.encode (u p i) w)) at h
    simpa only [HilbertCode.decode_encode] using h
  have hb0 : b i ≠ 0 := by
    intro hz
    simpa only [hz,norm_zero,zero_ne_one] using (hb i).1
  have heq : v = (d * (b i)⁻¹) • w := by
    dsimp only [w]
    rw [smul_smul,mul_assoc,inv_mul_cancel₀ hb0,mul_one]
    exact hvd
  have hwn : ‖d * (b i)⁻¹‖ = 1 := by rw [norm_mul,norm_inv,hdn,(hb i).1,inv_one,mul_one]
  have hwv := rayCanonical_unique hv hc hwn heq
  exact ⟨a,ha,(hb i).2.trans (congrArg (HilbertCode.encode (u p i)) hwv.symm)⟩
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [retained11 : DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

include retained11 in
lemma rawCode_of_cone (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (p : Arr I M.U 1) (i : I) (hL : Λ p = rawTupleKernel M p)
    (hm : ∀ j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (q : HilbertCode (M.ownKernel 0)) (hb : q.base = tupleParameter M p i)
    (hc : q.IsCanonical) (hu : q.IsUnimodular)
    (he : circleLp (M.ownKernel 0 (tupleParameter M p i)) (HilbertCode.circleRep q)
      (HilbertCode.measurable_circleRep_fixed q) ∈
      rawExactCone M i (M.ownKernel 0 (tupleParameter M p i)) p) :
    (p,q) ∈ rawLineGraph M Λ i := by
  let _ := retained11
  have hq : HilbertCode.encode (tupleParameter M p i)
      (circleLp (M.ownKernel 0 (tupleParameter M p i)) (HilbertCode.circleRep q)
        (HilbertCode.measurable_circleRep_fixed q)) = q := by
    rw [←hb,HilbertCode.circleLp_circleRep q hu,HilbertCode.encode_decode]
  have hcan : RayCanonical (hilbertTests (M.ownKernel 0 (tupleParameter M p i)))
      (circleLp (M.ownKernel 0 (tupleParameter M p i)) (HilbertCode.circleRep q)
        (HilbertCode.measurable_circleRep_fixed q)) := by
    rw [←hq] at hc
    change RayCanonical (hilbertTests (M.ownKernel 0 (tupleParameter M p i)))
      (HilbertCode.decode (HilbertCode.encode (tupleParameter M p i) _)) at hc
    simpa only [HilbertCode.decode_encode] using hc
  obtain ⟨f,hf,c,d,hd,he⟩ := he
  have he' : ∀ᵐ y ∂Λ p, ∏ j, f j (y j) = c := by
    rw [hL,rawTupleKernel,Kernel.map_apply _ (measurable_rawTuple M)]
    exact ae_map_descent _ (measurable_rawTuple M) he
  obtain ⟨a,ha,hai⟩ := canonical_smul_exact_tuple (M.ownKernel 0) Λ (tupleParameter M)
    p i hm _ hcan (circleLp_norm _ _ _) f hf c d he' hd
  exact ⟨a,ha,hai.trans hq⟩
end ArrayObjects.Object.Rolled

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
section
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
lemma operator_range_eq_span_tests {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (L : A →L[ℂ] B)
    (v : ℕ → A) (hv : DenseRange v) :
    (LinearMap.range L.toLinearMap).topologicalClosure =
      (Submodule.span ℂ (Set.range (fun n => L (v n)))).topologicalClosure := by
  apply le_antisymm
  · apply (operator_range_le_iff_tests L v hv _ (Submodule.isClosed_topologicalClosure _)).mpr
    intro n
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n,rfl⟩)
  · apply Submodule.topologicalClosure_mono
    apply Submodule.span_le.mpr
    rintro _ ⟨n,rfl⟩
    exact ⟨v n,rfl⟩

variable {P U Y : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ]
lemma MeasurableSection.circle (u : P → U) (hu : Measurable u) (f : P → Y → Circle)
    (hf : Measurable (Function.uncurry f)) :
    MeasurableSection (fun p => circleLp (κ (u p)) (f p)
      (hf.comp (measurable_const.prodMk measurable_id))) := by
  apply measurable_hilbert_encode u hu _ (fun py : P × Y => (f py.1 py.2 : ℂ))
    (measurable_subtype_coe.comp hf)
  intro p
  exact circleLp_coe _ _ _

lemma MeasurableSection.comp {Q : Type*} [MeasurableSpace Q] {u : P → U}
    {v : ∀ p, Lp ℂ 2 (κ (u p))} (hv : MeasurableSection v) (g : Q → P) (hg : Measurable g) :
    MeasurableSection (fun q => v (g q)) := Measurable.comp hv hg
end
namespace ArrayObjects.Object.Rolled
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma measurableSection_rawSlotTest (i : I) (n : ℕ) : MeasurableSection (rawSlotTest M i n) :=
  measurableSection_posteriorTest _ _ _ _ _ (measurable_plane _ _ _) n

lemma rawSlotTest_eq_operator (i : I) (p : Arr I M.U 1)
    (hp : MeasurePreserving (plane 0 0 i) (M.ownKernel 1 p)
      (M.ownKernel 0 (plane 0 0 i p))) (n : ℕ) :
    rawSlotTest M i n p = JoiningOperator.operator hp
      (MeasurePreserving.mk (measurable_slotRest M i) rfl)
      (hilbertTests ((M.ownKernel 1 p).map (slotRest M i)) n) :=
  posteriorTest_eq_operator _ _ _ _ _ (measurable_slotRest M i) p hp n

lemma rawSlotActive_eq_testSpan (hI : 2 ≤ Fintype.card I) (i : I) :
    ∀ᵐ p ∂M.parameterLaw 1,
      rawSlotActive M i (M.ownKernel 0 (plane 0 0 i p)) p = rawSlotTestSpan M i p := by
  have hm := ConditionalFibres.marginal (measurable_plane 0 0 i)
    (M.ownKernel_conditional 1) (M.plane_conditional hI 0 i)
  filter_upwards [hm] with p hp
  have hp' : MeasurePreserving (plane 0 0 i) (M.ownKernel 1 p)
      (M.ownKernel 0 (plane 0 0 i p)) := hp
  rw [rawSlotActive_eq M i _ p hp',rawSlotTestSpan]
  have ht : (fun n => rawSlotTest M i n p) = (fun n => JoiningOperator.operator hp'
      (MeasurePreserving.mk (measurable_slotRest M i) rfl)
      (hilbertTests ((M.ownKernel 1 p).map (slotRest M i)) n)) :=
    funext (rawSlotTest_eq_operator M i p hp')
  rw [ht]
  exact operator_range_eq_span_tests _ _ (hilbertTests_dense _)

variable {P : Type*} [MeasurableSpace P]
lemma measurableSet_rawSlot_mem (i : I) (f : P → Arr I M.Y 0 → Circle)
    (hf : Measurable (Function.uncurry f)) :
    MeasurableSet {pq : P × Arr I M.U 1 | circleLp (M.ownKernel 0 (plane 0 0 i pq.2)) (f pq.1)
      (hf.comp (measurable_const.prodMk measurable_id)) ∈ rawSlotTestSpan M i pq.2} := by
  apply measurableSet_section_mem_span ((measurable_plane _ _ _).comp measurable_snd)
    (fun n => (measurableSection_rawSlotTest M i n).comp Prod.snd measurable_snd)
  exact MeasurableSection.circle _ ((measurable_plane _ _ _).comp measurable_snd)
    (fun pq => f pq.1) (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

lemma measurable_rawSlotIndicator (i : I) (f : P → Arr I M.Y 0 → Circle)
    (hf : Measurable (Function.uncurry f)) : Measurable (Function.uncurry (rawSlotIndicator M i f hf)) := by
  classical
  change Measurable (fun pq : P × Arr I M.U 1 => decide
    (circleLp (M.ownKernel 0 (plane 0 0 i pq.2)) (f pq.1)
      (hf.comp (measurable_const.prodMk measurable_id)) ∈ rawSlotTestSpan M i pq.2))
  apply measurable_to_bool
  simpa only [Set.preimage,Set.mem_singleton_iff,decide_eq_true_eq] using
    measurableSet_rawSlot_mem M i f hf

lemma rawSlotIndicator_eq_true_iff (i : I) (f : P → Arr I M.Y 0 → Circle)
    (hf : Measurable (Function.uncurry f)) (p : P) (q : Arr I M.U 1) :
    rawSlotIndicator M i f hf p q = true ↔
      circleLp (M.ownKernel 0 (plane 0 0 i q)) (f p)
        (hf.comp (measurable_const.prodMk measurable_id)) ∈ rawSlotTestSpan M i q := by
  classical
  exact decide_eq_true_iff
end ArrayObjects.Object.Rolled
end

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma independent_equal_indicators {f g : Ω → Bool}
    (hf : Measurable f) (hfg : IndepFun f g μ) (he : f =ᵐ[μ] g) :
    (∀ᵐ ω ∂μ, f ω = false) ∨ ∀ᵐ ω ∂μ, f ω = true := by
  have hi : IndepFun f f μ := hfg.congr Filter.EventuallyEq.rfl he.symm
  have hp := hi.measure_inter_preimage_eq_mul ({true} : Set Bool) ({true} : Set Bool)
    (measurableSet_singleton _) (measurableSet_singleton _)
  simp only [inter_self] at hp
  let p := μ (f ⁻¹' ({true} : Set Bool))
  have hfin : p ≠ ∞ := measure_ne_top _ _
  have hz : p = 0 ∨ p = 1 := by
    by_cases h : p = 0
    · exact Or.inl h
    · right
      apply (ENNReal.mul_right_inj h hfin).mp
      simpa only [p,mul_one] using hp.symm
  rcases hz with hz | ho
  · left
    have ha : ∀ᵐ ω ∂μ, ω ∉ f ⁻¹' ({true} : Set Bool) := by
      exact ae_iff.mpr (by simpa only [p,not_not,Set.ofPred_mem_eq] using hz)
    filter_upwards [ha] with ω hω
    cases h : f ω <;> simp_all
  · right
    exact (mem_ae_iff_prob_eq_one ((measurableSet_singleton true).preimage hf)).mpr ho
end

section
open MeasureTheory ProbabilityTheory
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
lemma product_equal_positive_indicators (f : X → Bool) (g : Y → Bool)
    (hf : Measurable f) (hg : Measurable g)
    (he : ∀ᵐ p ∂μ.prod ν, f p.1 = g p.2)
    (hp : μ {x | f x = true} ≠ 0) :
    (∀ᵐ x ∂μ, f x = true) ∧ ∀ᵐ y ∂ν, g y = true := by
  have h := independent_equal_indicators (hf.comp measurable_fst) (indepFun_prod hf hg) he
  have htrue : ∀ᵐ p ∂μ.prod ν, f p.1 = true := by
    rcases h with hz | ht
    · have hfalse : ∀ᵐ x ∂μ, f x = false := by
        rw [←(measurePreserving_fst (μ := μ) (ν := ν)).map_eq]
        exact (ae_map_iff measurable_fst.aemeasurable (measurableSet_eq_fun hf measurable_const)).mpr hz
      apply False.elim
      apply hp
      simpa only [Bool.not_eq_false] using (ae_iff.mp hfalse)
    · exact ht
  constructor
  · rw [←(measurePreserving_fst (μ := μ) (ν := ν)).map_eq]
    exact (ae_map_iff measurable_fst.aemeasurable (measurableSet_eq_fun hf measurable_const)).mpr htrue
  · rw [←(measurePreserving_snd (μ := μ) (ν := ν)).map_eq]
    apply (ae_map_iff measurable_snd.aemeasurable (measurableSet_eq_fun hg measurable_const)).mpr
    filter_upwards [htrue,he] with p hp he
    exact he ▸ hp

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
  [StandardBorelSpace Ω] [StandardBorelSpace S] [StandardBorelSpace X] [StandardBorelSpace Y]
  {ρ : Measure Ω} [IsProbabilityMeasure ρ] {s : Ω → S} {x : Ω → X} {y : Ω → Y}
  {κ : Kernel S X} {l : Kernel S Y} [IsMarkovKernel κ] [IsMarkovKernel l]
omit [StandardBorelSpace Ω] [StandardBorelSpace S] [StandardBorelSpace X] in
lemma conditional_joint_ae_lift (hs : Measurable s) (hx : Measurable x)
    (hκ : HasCondDistrib x s κ ρ) {P : S → X → Prop}
    (hPm : MeasurableSet {p : S × X | P p.1 p.2})
    (hP : ∀ᵐ a ∂ρ.map s, ∀ᵐ b ∂κ a, P a b) : ∀ᵐ ω ∂ρ, P (s ω) (x ω) := by
  have h : ∀ᵐ p ∂(ρ.map s) ⊗ₘ κ, P p.1 p.2 := (Measure.ae_compProd_iff hPm).mpr hP
  rw [←hκ.map_eq] at h
  exact ae_of_ae_map (hs.prodMk hx).aemeasurable h

lemma conditional_equal_positive_indicators
    (hs : Measurable s) (hx : Measurable x) (hy : Measurable y)
    (hκ : HasCondDistrib (fun ω => (x ω,y ω)) s (κ ×ₖ l) ρ)
    (f : S → X → Bool) (g : S → Y → Bool)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (he : ∀ᵐ ω ∂ρ, f (s ω) (x ω) = g (s ω) (y ω))
    (hp : ∀ᵐ a ∂ρ.map s, κ a {z | f a z = true} ≠ 0) :
    ∀ᵐ ω ∂ρ, f (s ω) (x ω) = true ∧ g (s ω) (y ω) = true := by
  have hd := conditional_ae_descent (κ := κ ×ₖ l)
    (P := fun a p => f a p.1 = g a p.2) hs (hx.prodMk hy) hκ he
  have ht : ∀ᵐ a ∂ρ.map s, ∀ᵐ p ∂(κ ×ₖ l) a, f a p.1 = true ∧ g a p.2 = true := by
    filter_upwards [hd,hp] with a ha hp
    rw [Kernel.prod_apply] at ha ⊢
    have h := product_equal_positive_indicators (f a) (g a)
      (hf.comp (measurable_const.prodMk measurable_id))
      (hg.comp (measurable_const.prodMk measurable_id)) ha hp
    exact (measurePreserving_fst.quasiMeasurePreserving.ae h.1).and
      (measurePreserving_snd.quasiMeasurePreserving.ae h.2)
  apply conditional_joint_ae_lift hs (hx.prodMk hy) hκ _ ht
  exact ((measurableSet_eq_fun (hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
    measurable_const).inter (measurableSet_eq_fun
      (hg.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))) measurable_const))
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

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
local instance instFactNeENNRealOfNatTop_13 : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
omit [DecidableEq I] in
lemma parameterCoordinate_conditional (i : I) :
    HasCondDistrib (id : Arr I M.U 1 → Arr I M.U 1) (plane 0 0 i)
      (M.parameterCoordinateKernel i) (M.parameterLaw 1) :=
  ⟨((measurable_plane _ _ _).prodMk measurable_id).aemeasurable,
      (compProd_map_condDistrib measurable_id.aemeasurable).symm⟩

omit [DecidableEq I] in
lemma coordinate_conditional_descent (i : I) {P : Arr I M.U 0 → Arr I M.U 1 → Prop}
    (hP : ∀ᵐ p ∂M.parameterLaw 1, P (plane 0 0 i p) p) :
    ∀ᵐ u ∂M.parameterLaw 0, ∀ᵐ p ∂M.parameterCoordinateKernel i u, P u p := by
  have h := conditional_ae_descent (κ := M.parameterCoordinateKernel i) (measurable_plane _ _ _) measurable_id
    (parameterCoordinate_conditional M i) hP
  rwa [M.parameterLaw_consistent 0 0 i] at h

lemma raw_diagonal_binary (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I) (i : I) :
    ∀ᵐ u ∂M.parameterLaw 0,
    ∀ᵐ pq ∂(M.parameterCoordinateKernel i u).prod (M.parameterCoordinateKernel i u),
    ∀ (f : I → Arr I M.Y 0 → Circle) (hf : ∀ j, Measurable (f j)) (c : Circle),
      (∀ᵐ y ∂M.ownKernel 1 pq.1, ∏ j, f j (plane 0 0 j y) = c) →
      let v := circleLp (M.ownKernel 0 u) (f i) (hf i)
      (rawSlotActive M i (M.ownKernel 0 u) pq.2).starProjection v = 0 ∨
      (rawSlotActive M i (M.ownKernel 0 u) pq.2).starProjection v = v := by
  let P : Arr I M.U 0 → (Arr I M.U 1 × Arr I M.U 1) → Prop := fun u pq =>
    ∀ (f : I → Arr I M.Y 0 → Circle) (hf : ∀ j, Measurable (f j)) (c : Circle),
      (∀ᵐ y ∂M.ownKernel 1 pq.1, ∏ j, f j (plane 0 0 j y) = c) →
      let v := circleLp (M.ownKernel 0 u) (f i) (hf i)
      (rawSlotActive M i (M.ownKernel 0 u) pq.2).starProjection v = 0 ∨
      (rawSlotActive M i (M.ownKernel 0 u) pq.2).starProjection v = v
  have h := conditional_ae_descent (P := P)
    ((measurable_plane 0 0 i).comp (measurable_plane 1 0 i))
    ((measurable_plane _ _ _).prodMk (measurable_plane _ _ _))
    (M.diagonal_parameter_product hM (by omega) i) (raw_row_line_projection M hM hk i i)
  rw [←Measure.map_map (measurable_plane 0 0 i) (measurable_plane 1 0 i),
    M.parameterLaw_consistent 1 0 i,M.parameterLaw_consistent 0 0 i] at h
  simpa only [Kernel.prod_apply] using h

omit [DecidableEq I] in
lemma raw_coordinate_marginal (hI : 2 ≤ Fintype.card I) (i : I) :
    ∀ᵐ u ∂M.parameterLaw 0, ∀ᵐ p ∂M.parameterCoordinateKernel i u,
      MeasurePreserving (plane 0 0 i) (M.ownKernel 1 p) (M.ownKernel 0 u) := by
  exact coordinate_conditional_descent M i
    (ConditionalFibres.marginal (measurable_plane 0 0 i)
      (M.ownKernel_conditional 1) (M.plane_conditional hI 0 i))

lemma raw_slot_mem_parameter_congr (i : I) (u v : Arr I M.U 0) (h : u = v)
    (p : Arr I M.U 1) (f : Arr I M.Y 0 → Circle) (hf : Measurable f) :
    (circleLp (M.ownKernel 0 u) f hf ∈ rawSlotActive M i (M.ownKernel 0 u) p) ↔
    (circleLp (M.ownKernel 0 v) f hf ∈ rawSlotActive M i (M.ownKernel 0 v) p) := by
  subst v
  rfl

lemma raw_diagonal_positive (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I) (i : I)
    (f : Arr I M.U 1 → I → Arr I M.Y 0 → Circle)
    (hf : ∀ j, Measurable (fun py : Arr I M.U 1 × Arr I M.Y 0 => f py.1 j py.2))
    (he : ∀ᵐ p ∂M.parameterLaw 1, ∃ c : Circle,
      ∀ᵐ y ∂M.ownKernel 1 p, ∏ j, f p j (plane 0 0 j y) = c) :
    ∀ᵐ p ∂M.parameterLaw 1,
      M.parameterCoordinateKernel i (plane 0 0 i p)
        {q | rawSlotIndicator M i (fun p => f p i) (hf i) p q = true} ≠ 0 := by
  have hI : 2 ≤ Fintype.card I := by omega
  have hq := coordinate_conditional_descent M i
    (P := fun u p => plane 0 0 i p = u) (Filter.Eventually.of_forall fun _ => rfl)
  have ht := coordinate_conditional_descent M i
    (P := fun _ p => rawSlotActive M i (M.ownKernel 0 (plane 0 0 i p)) p = rawSlotTestSpan M i p)
    (rawSlotActive_eq_testSpan M hI i)
  have hex := coordinate_conditional_descent M i (P := fun _ p => ∃ c : Circle,
      ∀ᵐ y ∂M.ownKernel 1 p, ∏ j, f p j (plane 0 0 j y) = c) he
  have hp : ∀ᵐ u ∂M.parameterLaw 0, ∀ᵐ p ∂M.parameterCoordinateKernel i u,
      M.parameterCoordinateKernel i (plane 0 0 i p)
        {q | rawSlotIndicator M i (fun p => f p i) (hf i) p q = true} ≠ 0 := by
    filter_upwards [raw_diagonal_binary M hM hk i,raw_coordinate_marginal M hI i,hq,ht,hex]
      with u hbin hm hq ht hex
    have hnon := active_projection_not_ae_zero (M.parameterCoordinateKernel i u)
      (fun p => rawSlotActive M i (M.ownKernel 0 u) p)
    filter_upwards [Measure.ae_ae_of_ae_prod hbin,hm,hq,hex,hnon] with p hbin hm hpu hex hnon
    obtain ⟨c, hc⟩ := hex
    let hf' : ∀ j, Measurable (f p j) := fun j => (hf j).comp (measurable_const.prodMk measurable_id)
    let v := circleLp (M.ownKernel 0 u) (f p i) (hf' i)
    have hva : v ∈ rawSlotActive M i (M.ownKernel 0 u) p := raw_tuple_active M i p _ hm (f p) hf' c hc
    have hne : v ≠ 0 := circleLp_ne_zero _ _ _
    intro hz
    rw [hpu] at hz
    have hnmem : ∀ᵐ q ∂M.parameterCoordinateKernel i u,
        rawSlotIndicator M i (fun p => f p i) (hf i) p q ≠ true := by
      apply ae_iff.mpr
      simpa only [not_not] using hz
    apply hnon v hva hne
    filter_upwards [hbin,hq,ht,hnmem] with q hbin hqu ht hnmem
    rcases hbin (f p) hf' c hc with hzero | hself
    · exact hzero
    · apply False.elim
      apply hnmem
      apply (rawSlotIndicator_eq_true_iff M i (fun p => f p i) (hf i) p q).mpr
      rw [←ht]

      have hmem := (rawSlotActive M i (M.ownKernel 0 u) q).starProjection_eq_self_iff.mp hself
      exact (raw_slot_mem_parameter_congr M i u _ hqu.symm q (f p i) (hf' i)).mp hmem
  have hmeas : MeasurableSet {p : Arr I M.U 1 |
      M.parameterCoordinateKernel i (plane 0 0 i p)
        {q | rawSlotIndicator M i (fun p => f p i) (hf i) p q = true} ≠ 0} := by
    have h := Kernel.measurable_kernel_prodMk_left
      (κ := (M.parameterCoordinateKernel i).comap (plane 0 0 i) (measurable_plane _ _ _))
      (measurableSet_eq_fun (measurable_rawSlotIndicator M i (fun p => f p i) (hf i)) (measurable_const (a := true)))
    exact (measurableSet_eq_fun h (measurable_const (a := (0 : ℝ≥0∞)))).compl
  apply conditional_ae_lift (κ := M.parameterCoordinateKernel i) (measurable_plane _ _ _) measurable_id
    (parameterCoordinate_conditional M i) hmeas
  rwa [M.parameterLaw_consistent 0 0 i]
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory
namespace FiniteKernel
variable {ι S Y : Type*} [Fintype ι] [MeasurableSpace S] [MeasurableSpace Y]
lemma map_pair (κ : ι → Kernel S Y) [∀ i, IsMarkovKernel (κ i)]
    (i j : ι) (hij : i ≠ j) :
    (pi κ).map (fun y => (y i,y j)) = κ i ×ₖ κ j := by
  ext s : 1
  rw [Kernel.map_apply _ ((measurable_pi_apply i).prodMk (measurable_pi_apply j)),pi_apply,Kernel.prod_apply]
  have hi : iIndepFun (fun i : ι => Function.eval i) (Measure.pi (fun i => κ i s)) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  rw [(hi.indepFun hij).map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable,
    (measurePreserving_eval (fun i => κ i s) i).map_eq,
    (measurePreserving_eval (fun i => κ i s) j).map_eq]
end FiniteKernel
namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
lemma parameter_pair_geometry (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (a j t : I) (hjt : j ≠ t) :
    HasCondDistrib (fun e => (plane 1 (Fin.last 1) j e,plane 1 (Fin.last 1) t e))
      (plane 1 0 a)
      ((M.parameterCoordinateKernel a).comap (plane 0 0 j) (measurable_plane _ _ _) ×ₖ
       (M.parameterCoordinateKernel a).comap (plane 0 0 t) (measurable_plane _ _ _))
      (M.parameterLaw 2) := by
  have hpair : ({j,t} : Finset I) ≠ Finset.univ := by
    intro h
    have := pair_complement_nonempty hk j t
    simp only [h,Finset.compl_univ,Finset.not_nonempty_empty] at this
  let j' : ({j,t} : Finset I) := ⟨j,by simp⟩
  let t' : ({j,t} : Finset I) := ⟨t,by simp⟩
  have hne : j' ≠ t' := fun h => hjt (congrArg Subtype.val h)
  have h := (parameter_geometry M hM (by omega) a {j,t} hpair).comp_left
    ((measurable_pi_apply j').prodMk (measurable_pi_apply t'))
  rw [FiniteKernel.map_pair _ j' t' hne] at h
  exact h
end ArrayObjects.Object.Rolled
end

namespace ArrayObjects.Object.Rolled

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

section CircleSlotIndicators

attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma rawSlotIndicator_on_square (hI : 2 ≤ Fintype.card I) (a j : I)
    (f : Arr I M.U 1 → Arr I M.Y 0 → Circle)
    (hf : Measurable (Function.uncurry f)) :
    ∀ᵐ e ∂M.parameterLaw 2,
      rawSlotIndicator M a f hf (plane 1 0 a e) (plane 1 (Fin.last 1) j e) = true ↔
      circleLp (M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))) (f (plane 1 0 a e))
        (hf.comp (measurable_const.prodMk measurable_id)) ∈
      rawSlotActive M a (M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))) (plane 1 (Fin.last 1) j e) := by
  have hmp : MeasurePreserving (plane 1 (Fin.last 1) j) (M.parameterLaw 2) (M.parameterLaw 1) :=
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
  filter_upwards [hmp.quasiMeasurePreserving.ae (rawSlotActive_eq_testSpan M hI a)] with e he
  rw [rawSlotIndicator_eq_true_iff,←he]
  have hloc : plane 0 0 j (plane 1 0 a e) = plane 0 0 a (plane 1 (Fin.last 1) j e) := by
    funext x
    simp only [plane]
    congr 1
    funext t
    fin_cases t <;> rfl

  rw [hloc]

lemma raw_row_membership_forced (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I) (a j : I)
    (f : Arr I M.U 1 → I → Arr I M.Y 0 → Circle)
    (hf : ∀ i, Measurable (fun py : Arr I M.U 1 × Arr I M.Y 0 => f py.1 i py.2))
    (he : ∀ᵐ p ∂M.parameterLaw 1, ∃ c : Circle,
      ∀ᵐ y ∂M.ownKernel 1 p, ∏ i, f p i (plane 0 0 i y) = c) :
    ∀ᵐ e ∂M.parameterLaw 2,
      circleLp (M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))) (f (plane 1 0 a e) j)
        ((hf j).comp (measurable_const.prodMk measurable_id)) ∈
      rawSlotActive M a (M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))) (plane 1 (Fin.last 1) j e) := by
  have hforce (t : I) (hat : a ≠ t) :
      ∀ᵐ e ∂M.parameterLaw 2,
      rawSlotIndicator M a (fun p => f p a) (hf a) (plane 1 0 a e) (plane 1 (Fin.last 1) a e) = true ∧
      rawSlotIndicator M a (fun p => f p t) (hf t) (plane 1 0 a e) (plane 1 (Fin.last 1) t e) = true := by
    apply conditional_equal_positive_indicators (measurable_plane _ _ _) (measurable_plane _ _ _)
      (measurable_plane _ _ _) (parameter_pair_geometry M hM hk a a t hat)
      (rawSlotIndicator M a (fun p => f p a) (hf a)) (rawSlotIndicator M a (fun p => f p t) (hf t))
      (measurable_rawSlotIndicator M a _ _) (measurable_rawSlotIndicator M a _ _)
      (raw_row_indicators_equal M hM hk a a t hat f hf he)
    rw [M.parameterLaw_consistent 1 0 a]
    exact raw_diagonal_positive M hM hk a f hf he
  have hind : ∀ᵐ e ∂M.parameterLaw 2,
      rawSlotIndicator M a (fun p => f p j) (hf j) (plane 1 0 a e) (plane 1 (Fin.last 1) j e) = true := by
    by_cases haj : a = j
    · subst j
      have hex : ∃ t : I, a ≠ t := by
        by_contra! h
        have hc : Fintype.card I ≤ 1 := Fintype.card_le_one_iff.mpr (fun x y => (h x).symm.trans (h y))
        omega
      obtain ⟨t,hat⟩ := hex
      exact (hforce t hat).mono fun _ h => h.1
    · exact (hforce j haj).mono fun _ h => h.2
  filter_upwards [hind,rawSlotIndicator_on_square M (by omega) a j (fun p => f p j) (hf j)] with e he hh
  exact hh.mp he

omit [DecidableEq I] in
lemma parameter_cell_commute (a j : I) (e : Arr I M.U 2) :
    tupleParameter M (plane 1 0 a e) j = tupleParameter M (plane 1 (Fin.last 1) j e) a := by
  funext x
  simp only [tupleParameter,plane]
  congr 1
  funext t
  fin_cases t <;> rfl

omit [DecidableEq I] in
lemma rawExactCone_parameter_congr (i : I) (u v : Arr I M.U 0) (h : u = v)
    (p : Arr I M.U 1) (f : Arr I M.Y 0 → Circle) (hf : Measurable f) :
    (circleLp (M.ownKernel 0 u) f hf ∈ rawExactCone M i (M.ownKernel 0 u) p) ↔
    (circleLp (M.ownKernel 0 v) f hf ∈ rawExactCone M i (M.ownKernel 0 v) p) := by
  subst v
  rfl

lemma rawLineGraph_row_inclusion (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p)) (a j : I) :
    ∀ᵐ e ∂M.parameterLaw 2, ∀ q : HilbertCode (M.ownKernel 0),
      (plane 1 0 a e,q) ∈ rawLineGraph M Λ j →
      (plane 1 (Fin.last 1) j e,q) ∈ rawLineGraph M Λ a := by
  classical
  obtain ⟨D,s,hD,hs,hbase,hmem,_,hcover⟩ := exactCode_sections (M.ownKernel 0) Λ
    (tupleParameter M) (measurable_tupleParameter M) hk hm hind
  let f : ℕ → Arr I M.U 1 → I → Arr I M.Y 0 → Circle :=
    fun n p i y => if p ∈ D n then HilbertCode.circleRep (s n p i) y else 1
  have hf (n i) : Measurable (fun py : Arr I M.U 1 × Arr I M.Y 0 => f n py.1 i py.2) := by
    exact (HilbertCode.measurable_circleRep.comp
      ((((measurable_pi_apply i).comp (hs n)).comp measurable_fst).prodMk measurable_snd)).ite
      ((hD n).preimage measurable_fst) measurable_const
  have hex (n) : ∀ᵐ p ∂M.parameterLaw 1, ∃ c : Circle,
      ∀ᵐ y ∂M.ownKernel 1 p, ∏ i, f n p i (plane 0 0 i y) = c := by
    filter_upwards [hL] with p hp
    by_cases hpd : p ∈ D n
    · obtain ⟨c,hc⟩ := exactCode_circle_tuple (M.ownKernel 0) Λ (tupleParameter M) (hm p) (hmem n p hpd)
      rw [hp,rawTupleKernel,Kernel.map_apply _ (measurable_rawTuple M)] at hc
      refine ⟨c,?_⟩
      have he := ae_of_ae_map (measurable_rawTuple M).aemeasurable hc
      simpa only [f,ite_eq_left hpd,rawTuple] using he
    · exact ⟨1,Filter.Eventually.of_forall (fun _ => by simp only [f,ite_eq_right hpd,Finset.prod_const_one])⟩
  have hrow : MeasurePreserving (plane 1 0 a) (M.parameterLaw 2) (M.parameterLaw 1) :=
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
  have hcol : MeasurePreserving (plane 1 (Fin.last 1) j) (M.parameterLaw 2) (M.parameterLaw 1) :=
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
  filter_upwards [ae_all_iff.mpr (fun n => raw_row_membership_forced M hM hk a j (f n) (hf n) (hex n)),
    raw_row_active_to_column_exact M hM hk a j,
    hrow.quasiMeasurePreserving.ae (ae_all_iff.mpr hex),hcol.quasiMeasurePreserving.ae hL]
    with e hforce hcone hexes hLe
  intro q hq
  obtain ⟨b,hb,hbi⟩ := hq
  dsimp only [Prod.fst,Prod.snd] at hb hbi
  obtain ⟨n,hnd,hns⟩ := hcover (_,b) hb
  dsimp only [Prod.fst,Prod.snd] at hnd hns
  have hfq : f n (plane 1 0 a e) j = HilbertCode.circleRep q := by
    funext y
    dsimp only [f]
    rw [ite_eq_left hnd,hns,hbi]
  obtain ⟨c,hc⟩ := hexes n
  have hce := hcone (f n (plane 1 0 a e))
    (fun i => (hf n i).comp (measurable_const.prodMk measurable_id)) c hc (hforce n)
  have hcc : q.IsCanonical ∧ q.IsUnimodular := by
    rw [←hbi]
    exact hb.2.1 j
  have hqb : q.base = tupleParameter M (plane 1 (Fin.last 1) j e) a := by
    rw [←hbi]
    exact (hb.1 j).trans (parameter_cell_commute M a j e)
  apply rawCode_of_cone M Λ _ a hLe (hm _) q hqb hcc.1 hcc.2
  change circleLp (M.ownKernel 0 (tupleParameter M (plane 1 0 a e) j)) _ _ ∈
    rawExactCone M a (M.ownKernel 0 (tupleParameter M (plane 1 0 a e) j)) _ at hce
  apply (rawExactCone_parameter_congr M a _ _ (parameter_cell_commute M a j e)
    _ q.circleRep (HilbertCode.measurable_circleRep_fixed q)).mp
  simpa only [hfq] using hce
end CircleSlotIndicators


universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
omit [DecidableEq I] in
lemma rawLineGraph_base {Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)}
    {p : Arr I M.U 1} {i : I} {q : HilbertCode (M.ownKernel 0)}
    (h : (p,q) ∈ rawLineGraph M Λ i) : q.base = tupleParameter M p i := by
  obtain ⟨a,ha,hq⟩ := h
  dsimp only [Prod.fst,Prod.snd] at ha hq
  rw [←hq]
  exact ha.1 i
omit [DecidableEq I] in
lemma rawLineGraph_canonical {Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)}
    {p : Arr I M.U 1} {i : I} {q : HilbertCode (M.ownKernel 0)}
    (h : (p,q) ∈ rawLineGraph M Λ i) : q.IsCanonical ∧ q.IsUnimodular := by
  obtain ⟨a,ha,hq⟩ := h
  dsimp only [Prod.fst,Prod.snd] at ha hq
  rw [←hq]
  exact ha.2.1 i
lemma rawLineGraph_separated (hk : 3 ≤ Fintype.card I)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (p : Arr I M.U 1) (i : I) (q r : HilbertCode (M.ownKernel 0))
    (hq : (p,q) ∈ rawLineGraph M Λ i) (hr : (p,r) ∈ rawLineGraph M Λ i)
    (hne : q ≠ r) : 1 ≤ HilbertCode.distance q r := by
  obtain ⟨a,ha,hai⟩ := hq
  obtain ⟨b,hb,hbi⟩ := hr
  dsimp only [Prod.fst,Prod.snd] at ha hb hai hbi
  have h := HilbertCode.exact_codes_dichotomy (κ := M.ownKernel 0) hk (Λ p) a b
    (fun j => (ha.1 j).trans (hb.1 j).symm) ha.2.1 hb.2.1
    (fun j => by simpa only [ha.1 j] using hm p j) (hind p) ha.2.2 hb.2.2
  rcases h with h | h
  · exact (hne (hai.symm.trans ((congrFun h i).trans hbi))).elim
  · simpa only [hai,hbi] using h i
end ArrayObjects.Object.Rolled

section
open MeasureTheory ProbabilityTheory Set
variable {P Z U : Type*} [MeasurableSpace P] [MeasurableSpace Z] [MeasurableSpace U]

omit [MeasurableSpace Z] in

lemma iid_random_set_descent (μ : Measure P) [IsProbabilityMeasure μ]
    (S : P → Set Z) (he : ∀ᵐ pq ∂μ.prod μ, S pq.1 = S pq.2) :
    ∀ᵐ p ∂μ, S p = {z | ∀ᵐ q ∂μ, z ∈ S q} := by
  filter_upwards [Measure.ae_ae_of_ae_prod he] with p hp
  ext z
  constructor
  · intro hz
    filter_upwards [hp] with q hq
    rwa [←hq]
  · intro hz
    obtain ⟨q,hq,hzq⟩ := (hp.and hz).exists
    rwa [hq]

lemma measurableSet_essentialMembership (κ : Kernel U P) [IsSFiniteKernel κ]
    {S : Set (P × Z)} (hS : MeasurableSet S) :
    MeasurableSet (essentialMembership κ S) := by
  have h := Kernel.measurable_kernel_prodMk_left (κ := κ.comap Prod.fst measurable_fst)
    (hS.preimage (measurable_snd.prodMk measurable_fst.snd))
  exact measurableSet_eq_fun h measurable_const

lemma mem_essentialMembership_iff (κ : Kernel U P) [IsMarkovKernel κ]
    {S : Set (P × Z)} (hS : MeasurableSet S) (u : U) (z : Z) :
    (u,z) ∈ essentialMembership κ S ↔ ∀ᵐ p ∂κ u, (p,z) ∈ S := by
  exact (mem_ae_iff_prob_eq_one (hS.preimage (measurable_id.prodMk measurable_const))).symm

lemma conditional_random_set_descent (κ : Kernel U P) [IsMarkovKernel κ]
    {S : Set (P × Z)} (hS : MeasurableSet S) (u : U)
    (he : ∀ᵐ pq ∂(κ u).prod (κ u), {z | (pq.1,z) ∈ S} = {z | (pq.2,z) ∈ S}) :
    ∀ᵐ p ∂κ u, {z | (p,z) ∈ S} = {z | (u,z) ∈ essentialMembership κ S} := by
  filter_upwards [iid_random_set_descent (κ u) (fun p => {z | (p,z) ∈ S}) he] with p hp
  rw [hp]
  ext z
  exact (mem_essentialMembership_iff κ hS u z).symm
end

section
open MeasureTheory ProbabilityTheory Set
variable {P Z : Type*} [MeasurableSpace P]
lemma iid_random_set_equality (μ : Measure P) [IsProbabilityMeasure μ]
    (S : P → Set Z) (he : ∀ᵐ pq ∂μ.prod μ, S pq.1 ⊆ S pq.2) :
    ∀ᵐ pq ∂μ.prod μ, S pq.1 = S pq.2 := by
  have hs : MeasurePreserving (Prod.swap : P × P → P × P) (μ.prod μ) (μ.prod μ) :=
    ⟨measurable_swap,Measure.prod_swap⟩
  filter_upwards [he,hs.quasiMeasurePreserving.ae he] with pq hp hq
  exact Set.Subset.antisymm hp hq
end

section
open MeasureTheory ProbabilityTheory Set
variable {U Y : Type*} [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  (κ : Kernel U Y) [IsMarkovKernel κ]

lemma separated_family_sections (S : Set (U × HilbertCode κ)) (hS : MeasurableSet S)
    (hb : ∀ u q, (u,q) ∈ S → q.base = u)
    (hsep : ∀ u q r, (u,q) ∈ S → (u,r) ∈ S → q ≠ r → 1 ≤ HilbertCode.distance q r) :
    ∃ (D : ℕ → Set U) (s : ℕ → U → HilbertCode κ),
      (∀ n, MeasurableSet (D n)) ∧ (∀ n, Measurable (s n)) ∧
      (∀ n u, (s n u).base = u) ∧
      (∀ n u, u ∈ D n → (u,s n u) ∈ S) ∧
      (∀ u q, (u,q) ∈ S → ∃ n, u ∈ D n ∧ s n u = q) := by
  let : StandardBorelSpace S := hS.standardBorel
  obtain ⟨C,_,hcover,_,hemb⟩ := HilbertCode.separated_branches
    (fun x : S => x.1.1) measurable_subtype_coe.fst
    (fun x : S => x.1.2) measurable_subtype_coe.snd
    (fun x y he => (hb _ _ x.property).trans (he.trans (hb _ _ y.property).symm))
    1 (by norm_num) (by
      intro x y he hne
      apply hsep x.1.1 x.1.2 y.1.2 x.property
      · rw [he]
        exact y.property
      · intro h
        exact hne (Subtype.ext (Prod.ext he h)))
  obtain ⟨D,s,hD,hs,hzero,hmem,hcov⟩ := measurable_branch_sections
    (fun x : S => x.1.1) (fun x : S => x.1.2) measurable_subtype_coe.snd
    (fun u => HilbertCode.encode u 0) (MeasurableSection.zero measurable_id) C hcover hemb
  refine ⟨D,s,hD,hs,?_,?_,?_⟩
  · intro n u
    by_cases hu : u ∈ D n
    · obtain ⟨x,hx,he⟩ := hmem n u hu
      rw [he]
      exact (hb _ _ x.property).trans hx
    · rw [hzero n u hu]
      rfl
  · intro n u hu
    obtain ⟨x,hx,he⟩ := hmem n u hu
    rw [he,←hx]
    exact x.property
  · intro u q hq
    exact hcov ⟨(u,q),hq⟩
end

section
open MeasureTheory ProbabilityTheory Set
variable {P U Z : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Z]
lemma measurableSet_enumerated_fibre_eq
    (S : Set (P × Z)) (T : Set (U × Z)) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (f : P → U) (hf : Measurable f)
    (D : ℕ → Set P) (s : ℕ → P → Z) (hD : ∀ n, MeasurableSet (D n))
    (hs : ∀ n, Measurable (s n))
    (hsm : ∀ n p, p ∈ D n → (p,s n p) ∈ S)
    (hsc : ∀ p z, (p,z) ∈ S → ∃ n, p ∈ D n ∧ s n p = z)
    (E : ℕ → Set U) (t : ℕ → U → Z) (hE : ∀ n, MeasurableSet (E n))
    (ht : ∀ n, Measurable (t n))
    (htm : ∀ n u, u ∈ E n → (u,t n u) ∈ T)
    (htc : ∀ u z, (u,z) ∈ T → ∃ n, u ∈ E n ∧ t n u = z) :
    MeasurableSet {p | {z | (p,z) ∈ S} = {z | (f p,z) ∈ T}} := by
  have he : {p | {z | (p,z) ∈ S} = {z | (f p,z) ∈ T}} =
      {p | (∀ n, p ∈ D n → (f p,s n p) ∈ T) ∧
           (∀ n, f p ∈ E n → (p,t n (f p)) ∈ S)} := by
    ext p
    constructor
    · intro hp
      constructor
      · intro n hn
        exact Set.ext_iff.mp hp (s n p) |>.mp (hsm n p hn)
      · intro n hn
        exact Set.ext_iff.mp hp (t n (f p)) |>.mpr (htm n (f p) hn)
    · rintro ⟨ha,hb⟩
      ext z
      constructor
      · intro hz
        obtain ⟨n,hn,rfl⟩ := hsc p z hz
        exact ha n hn
      · intro hz
        obtain ⟨n,hn,rfl⟩ := htc (f p) z hz
        exact hb n hn
  rw [he]
  change MeasurableSet ({p | ∀ n, p ∈ D n → (f p,s n p) ∈ T} ∩
    {p | ∀ n, f p ∈ E n → (p,t n (f p)) ∈ S})
  simp only [Set.ofPred_forall]
  refine (MeasurableSet.iInter fun n => ?_).inter (MeasurableSet.iInter fun n => ?_)
  · convert (hD n).compl.union (hT.preimage (hf.prodMk (hs n))) using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    simp only [mem_ofPred_eq,mem_union,mem_compl_iff,mem_preimage]
    tauto
  · convert ((hE n).preimage hf).compl.union (hS.preimage (measurable_id.prodMk ((ht n).comp hf))) using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    simp only [mem_ofPred_eq,mem_union,mem_compl_iff,mem_preimage,Function.comp_apply,id_eq]
    tauto
end

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory Set

section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))

include hk hm hind in
lemma measurableSet_rawLineGraph (i : I) : MeasurableSet (rawLineGraph M Λ i) :=
  measurableSet_exactCodeSlot (M.ownKernel 0) Λ (tupleParameter M) (measurable_tupleParameter M) hk hm hind i

include hM hk hL hm hind in
lemma rawLineGraph_conditional_descent (i : I) :
    ∀ᵐ u ∂M.parameterLaw 0, ∀ᵐ p ∂M.parameterCoordinateKernel i u,
      {q | (p,q) ∈ rawLineGraph M Λ i} =
        {q | (u,q) ∈ essentialMembership (M.parameterCoordinateKernel i) (rawLineGraph M Λ i)} := by
  have h := conditional_ae_descent
    (P := fun _ pq => {q | (pq.1,q) ∈ rawLineGraph M Λ i} ⊆ {q | (pq.2,q) ∈ rawLineGraph M Λ i})
    ((measurable_plane 0 0 i).comp (measurable_plane 1 0 i))
    ((measurable_plane _ _ _).prodMk (measurable_plane _ _ _))
    (M.diagonal_parameter_product hM (by omega) i)
    (rawLineGraph_row_inclusion M hM hk Λ hL hm hind i i)
  rw [←Measure.map_map (measurable_plane 0 0 i) (measurable_plane 1 0 i),
    M.parameterLaw_consistent 1 0 i,M.parameterLaw_consistent 0 0 i] at h
  simp only [Kernel.prod_apply] at h
  filter_upwards [h] with u hu
  exact conditional_random_set_descent (M.parameterCoordinateKernel i)
    (measurableSet_rawLineGraph M hk Λ hm hind i) u
    (iid_random_set_equality _ (fun p => {q | (p,q) ∈ rawLineGraph M Λ i}) hu)

include hM hk hL hm hind in
lemma exists_localLineGraph (i : I) :
    ∃ S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)),
      MeasurableSet S ∧
      (∀ u q, (u,q) ∈ S → q.base = u ∧ q.IsCanonical ∧ q.IsUnimodular) ∧
      (∀ u q r, (u,q) ∈ S → (u,r) ∈ S → q ≠ r → 1 ≤ HilbertCode.distance q r) ∧
      (∀ᵐ p ∂M.parameterLaw 1, {q | (p,q) ∈ rawLineGraph M Λ i} =
        {q | (tupleParameter M p i,q) ∈ S}) := by
  let S₀ := essentialMembership (M.parameterCoordinateKernel i) (rawLineGraph M Λ i)
  have hS₀ : MeasurableSet S₀ := measurableSet_essentialMembership _
    (measurableSet_rawLineGraph M hk Λ hm hind i)
  have ha := rawLineGraph_conditional_descent M hM hk Λ hL hm hind i
  have hb := coordinate_conditional_descent M i
    (P := fun u p => tupleParameter M p i = u) (Filter.Eventually.of_forall fun _ => rfl)
  let Q : Arr I M.U 0 → Prop := fun u =>
    (∀ q, (u,q) ∈ S₀ → q.base = u ∧ q.IsCanonical ∧ q.IsUnimodular) ∧
    (∀ q r, (u,q) ∈ S₀ → (u,r) ∈ S₀ → q ≠ r → 1 ≤ HilbertCode.distance q r)
  have hQ : ∀ᵐ u ∂M.parameterLaw 0, Q u := by
    filter_upwards [ha,hb] with u ha hb
    obtain ⟨p,hp,hpu⟩ := (ha.and hb).exists
    have heq (q) : (p,q) ∈ rawLineGraph M Λ i ↔ (u,q) ∈ S₀ := Set.ext_iff.mp hp q
    constructor
    · intro q hq
      have hq' := (heq q).mpr hq
      exact ⟨(rawLineGraph_base M hq').trans hpu,rawLineGraph_canonical M hq'⟩
    · intro q r hq hr hne
      exact rawLineGraph_separated M hk Λ hm hind p i q r ((heq q).mpr hq) ((heq r).mpr hr) hne
  have hn : NullMeasurableSet {u | Q u} (M.parameterLaw 0) :=
    NullMeasurableSet.congr (nullMeasurableSet_univ (μ := M.parameterLaw 0))
      (by filter_upwards [hQ] with u h; exact propext (iff_of_true trivial h))
  obtain ⟨A,hA,hAm,hAe⟩ := hn.exists_measurable_subset_ae_eq
  let S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)) := (Prod.fst ⁻¹' A) ∩ S₀
  have hS : MeasurableSet S := (hAm.preimage measurable_fst).inter hS₀
  have hSb (u q) (hq : (u,q) ∈ S) : q.base = u ∧ q.IsCanonical ∧ q.IsUnimodular :=
    (hA hq.1).1 q hq.2
  have hSs (u q r) (hq : (u,q) ∈ S) (hr : (u,r) ∈ S) (hne : q ≠ r) :
      1 ≤ HilbertCode.distance q r := (hA hq.1).2 q r hq.2 hr.2 hne
  obtain ⟨E,t,hE,ht,_,htm,htc⟩ := separated_family_sections (M.ownKernel 0) S hS
    (fun u q hq => (hSb u q hq).1) hSs
  obtain ⟨D,s,hD,hs,_,hsm,_,hsc⟩ := exactCode_sections (M.ownKernel 0) Λ
    (tupleParameter M) (measurable_tupleParameter M) hk hm hind
  have hemeas : MeasurableSet {p | {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S}} :=
    measurableSet_enumerated_fibre_eq (rawLineGraph M Λ i) S
      (measurableSet_rawLineGraph M hk Λ hm hind i) hS (fun p => tupleParameter M p i)
      ((measurable_pi_apply i).comp (measurable_tupleParameter M))
      D (fun n p => s n p i) hD (fun n => (measurable_pi_apply i).comp (hs n))
      (fun n p hp => ⟨s n p,hsm n p hp,rfl⟩) (by
        intro p q hq
        obtain ⟨b,hb,hbi⟩ := hq
        obtain ⟨n,hn,he⟩ := hsc (p,b) hb
        exact ⟨n,hn,(congrFun he i).trans hbi⟩)
      E t hE ht htm htc
  refine ⟨S,hS,hSb,hSs,?_⟩
  apply conditional_ae_lift (κ := M.parameterCoordinateKernel i) (measurable_plane _ _ _) measurable_id
    (parameterCoordinate_conditional M i) hemeas
  rw [M.parameterLaw_consistent 0 0 i]
  filter_upwards [ha,hb,hQ,hAe] with u ha hb hQ hAe
  filter_upwards [ha,hb] with p hp hpu
  rw [hpu,hp]
  ext q
  exact (and_iff_right (hAe.mpr hQ)).symm
end

universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma localLineGraph_inclusion (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p))
    (S : I → Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)))
    (hS : ∀ i, ∀ᵐ p ∂M.parameterLaw 1, {q | (p,q) ∈ rawLineGraph M Λ i} =
      {q | (tupleParameter M p i,q) ∈ S i}) (a j : I) :
    ∀ᵐ u ∂M.parameterLaw 0, {q | (u,q) ∈ S j} ⊆ {q | (u,q) ∈ S a} := by
  have hrow : MeasurePreserving (plane 1 0 a) (M.parameterLaw 2) (M.parameterLaw 1) :=
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
  have hcol : MeasurePreserving (plane 1 (Fin.last 1) j) (M.parameterLaw 2) (M.parameterLaw 1) :=
    ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩
  have h : ∀ᵐ e ∂M.parameterLaw 2,
      {q | (tupleParameter M (plane 1 0 a e) j,q) ∈ S j} ⊆
      {q | (tupleParameter M (plane 1 0 a e) j,q) ∈ S a} := by
    filter_upwards [rawLineGraph_row_inclusion M hM hk Λ hL hm hind a j,
      hrow.quasiMeasurePreserving.ae (hS j),hcol.quasiMeasurePreserving.ae (hS a)] with e he hr hc
    rw [parameter_cell_commute M a j e] at hr ⊢
    rw [←hr,←hc]
    exact he
  have hd := ae_map_descent (P := fun u => {q | (u,q) ∈ S j} ⊆ {q | (u,q) ∈ S a}) (M.parameterLaw 2)
    ((measurable_plane 0 0 j).comp (measurable_plane 1 0 a)) h
  rwa [←Measure.map_map (measurable_plane 0 0 j) (measurable_plane 1 0 a),
    M.parameterLaw_consistent 1 0 a,M.parameterLaw_consistent 0 0 j] at hd

lemma exists_commonLocalLineGraph (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (Λ : Kernel (Arr I M.U 1) (I → Arr I M.Y 0)) [IsMarkovKernel Λ]
    (hL : Λ =ᵐ[M.parameterLaw 1] rawTupleKernel M)
    (hm : ∀ p j, MeasurePreserving (fun y : I → Arr I M.Y 0 => y j) (Λ p)
      (M.ownKernel 0 (tupleParameter M p j)))
    (hind : ∀ p j, iIndepFun (fun t : (Finset.univ.erase j : Finset I) =>
      fun y : I → Arr I M.Y 0 => y t) (Λ p)) :
    ∃ S : Set (Arr I M.U 0 × HilbertCode (M.ownKernel 0)),
      MeasurableSet S ∧
      (∀ u q, (u,q) ∈ S → q.base = u ∧ q.IsCanonical ∧ q.IsUnimodular) ∧
      (∀ u q r, (u,q) ∈ S → (u,r) ∈ S → q ≠ r → 1 ≤ HilbertCode.distance q r) ∧
      (∀ᵐ p ∂M.parameterLaw 1, ∀ i, {q | (p,q) ∈ rawLineGraph M Λ i} =
        {q | (tupleParameter M p i,q) ∈ S}) := by
  classical
  have hI : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  let i₀ : I := Classical.choice hI
  choose S hSm hSb hSs hSe using exists_localLineGraph M hM hk Λ hL hm hind
  have he (i : I) : ∀ᵐ u ∂M.parameterLaw 0, {q | (u,q) ∈ S i} = {q | (u,q) ∈ S i₀} := by
    filter_upwards [localLineGraph_inclusion M hM hk Λ hL hm hind S hSe i₀ i,
      localLineGraph_inclusion M hM hk Λ hL hm hind S hSe i i₀] with u ha hb
    exact Subset.antisymm ha hb
  have hep (i : I) : ∀ᵐ p ∂M.parameterLaw 1,
      {q | (tupleParameter M p i,q) ∈ S i} = {q | (tupleParameter M p i,q) ∈ S i₀} :=
    (show MeasurePreserving (plane 0 0 i) (M.parameterLaw 1) (M.parameterLaw 0) from
      ⟨measurable_plane _ _ _,M.parameterLaw_consistent _ _ _⟩).quasiMeasurePreserving.ae (he i)
  refine ⟨S i₀,hSm i₀,hSb i₀,hSs i₀,?_⟩
  filter_upwards [ae_all_iff.mpr hSe,ae_all_iff.mpr hep] with p h₁ h₂ i
  exact (h₁ i).trans (h₂ i)

end ArrayObjects.Object.Rolled

open MeasureTheory Set
variable {U Z : Type*} [MeasurableSpace U] [MeasurableSpace Z] [MeasurableEq Z]

lemma enumerate_without_repetition (S : Set (U × Z))
    (D : ℕ → Set U) (s : ℕ → U → Z)
    (hD : ∀ n, MeasurableSet (D n)) (hs : ∀ n, Measurable (s n))
    (hm : ∀ n u, u ∈ D n → (u,s n u) ∈ S)
    (hc : ∀ u z, (u,z) ∈ S → ∃ n, u ∈ D n ∧ s n u = z) :
    ∃ E : ℕ → Set U, (∀ n, MeasurableSet (E n)) ∧
      (∀ n, E n ⊆ D n) ∧
      (∀ n u, u ∈ E n → (u,s n u) ∈ S) ∧
      (∀ u z, (u,z) ∈ S → ∃ n, u ∈ E n ∧ s n u = z) ∧
      (∀ u n m, u ∈ E n → u ∈ E m → s n u = s m u → n = m) := by
  classical
  let E : ℕ → Set U := fun n => D n \ ⋃ m < n, {u | u ∈ D m ∧ s m u = s n u}
  have hED (n) : E n ⊆ D n := fun _ h => h.1
  refine ⟨E,?_,hED,(fun n u h => hm n u (hED n h)),?_,?_⟩
  · intro n
    exact (hD n).diff (MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ =>
      (hD m).inter (measurableSet_eq_fun (hs m) (hs n)))
  · intro u z hz
    have hex := hc u z hz
    let n := Nat.find hex
    have hn : u ∈ D n ∧ s n u = z := Nat.find_spec hex
    refine ⟨n,⟨hn.1,?_⟩,hn.2⟩
    intro hu
    obtain ⟨m,hem⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hmn,he⟩ := Set.mem_iUnion.mp hem
    exact Nat.find_min hex hmn ⟨he.1,he.2.trans hn.2⟩
  · intro u n m hn hm he
    have hnot (n m : ℕ) (hn : u ∈ E n) (hm : u ∈ E m) (he : s n u = s m u) : ¬n < m := by
      intro hnm
      exact hm.2 (Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨hnm,hn.1,he⟩⟩)
    exact Nat.le_antisymm (not_lt.mp (hnot m n hm hn he.symm)) (not_lt.mp (hnot n m hn hm he))

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_FibreMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory ProbabilityTheory Set
variable {U Y : Type*} [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  (κ : Kernel U Y) [IsMarkovKernel κ]
lemma separated_family_enumeration (S : Set (U × HilbertCode κ)) (hS : MeasurableSet S)
    (hb : ∀ u q, (u,q) ∈ S → q.base = u)
    (hsep : ∀ u q r, (u,q) ∈ S → (u,r) ∈ S → q ≠ r → 1 ≤ HilbertCode.distance q r) :
    Nonempty (BorelFibreEnumeration S) := by
  obtain ⟨D,s,hD,hs,_,hm,hc⟩ := separated_family_sections κ S hS hb hsep
  obtain ⟨E,hE,_,he,hec,heu⟩ := enumerate_without_repetition S D s hD hs hm hc
  exact ⟨⟨E,s,hE,hs,he,hec,heu⟩⟩
end

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {P U Y I : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

lemma exactCode_enumeration (hu : Measurable u) (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) :
    Nonempty (BorelFibreEnumeration (exactCodeSet κ Λ u)) := by
  obtain ⟨D,s,hD,hs,_,hm,_,hc⟩ := exactCode_sections κ Λ u hu hk hm hind
  obtain ⟨E,hE,_,he,hec,heu⟩ := enumerate_without_repetition (exactCodeSet κ Λ u)
    D s hD hs hm (fun p a ha => hc (p,a) ha)
  exact ⟨⟨E,s,hE,hs,he,hec,heu⟩⟩

end

section
open MeasureTheory ProbabilityTheory Set
variable {P Q U Y I : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace Q] [StandardBorelSpace Q]
  [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U) (row col : Q → I → P)

omit [StandardBorelSpace P] [StandardBorelSpace Q] [DecidableEq I] in
lemma measurableSet_exactSquareSet (hu : Measurable u) (hr : Measurable row) (hc : Measurable col) :
    MeasurableSet (exactSquareSet κ Λ u row col) := by
  have hrow (a : I) : MeasurableSet {eq : Q × (I → I → HilbertCode κ) |
      (row eq.1 a,eq.2 a) ∈ exactCodeSet κ Λ u} :=
    (measurableSet_exactCodeSet κ Λ u hu).preimage
      ((((measurable_pi_apply a).comp hr).comp measurable_fst).prodMk
        ((measurable_pi_apply a).comp measurable_snd))
  have hcol (s : I) : MeasurableSet {eq : Q × (I → I → HilbertCode κ) |
      (col eq.1 s,fun a => eq.2 a s) ∈ exactCodeSet κ Λ u} := by
    apply (measurableSet_exactCodeSet κ Λ u hu).preimage
    apply (((measurable_pi_apply s).comp hc).comp measurable_fst).prodMk
    exact Measurable.of_eval (fun a => (measurable_pi_apply s).comp
      ((measurable_pi_apply a).comp measurable_snd))
  convert (MeasurableSet.iInter hrow).inter (MeasurableSet.iInter hcol) using 1
  all_goals try with_reducible_and_instances rfl
  ext eq
  simp [exactSquareSet]

omit [StandardBorelSpace P] [MeasurableSpace Q] [StandardBorelSpace Q] [StandardBorelSpace U] in
lemma exactSquare_unique_cell (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p))
    {e : Q} {q r : I → I → HilbertCode κ}
    (hq : (e,q) ∈ exactSquareSet κ Λ u row col)
    (hr : (e,r) ∈ exactSquareSet κ Λ u row col) (a s : I) (he : q a s = r a s) : q = r := by
  have hc : (fun i => q i s) = fun i => r i s :=
    exactCode_unique_slot κ Λ u hk hm hind (hq.2 s) (hr.2 s) a he
  funext i
  exact exactCode_unique_slot κ Λ u hk hm hind (hq.1 i) (hr.1 i) s (congrFun hc i)

omit [StandardBorelSpace P] [MeasurableSpace Q] [StandardBorelSpace Q] [StandardBorelSpace U] in
lemma exactSquare_separated (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p))
    {e : Q} {q r : I → I → HilbertCode κ}
    (hq : (e,q) ∈ exactSquareSet κ Λ u row col)
    (hr : (e,r) ∈ exactSquareSet κ Λ u row col) (a s : I) (hne : q ≠ r) :
    1 ≤ HilbertCode.distance (q a s) (r a s) := by
  rcases HilbertCode.exact_codes_dichotomy hk (Λ (row e a)) (q a) (r a)
    (fun j => ((hq.1 a).1 j).trans ((hr.1 a).1 j).symm) (hq.1 a).2.1 (hr.1 a).2.1
    (fun j => by simpa only [(hq.1 a).1 j] using hm (row e a) j)
    (hind (row e a)) (hq.1 a).2.2 (hr.1 a).2.2 with h | h
  · exact (hne (exactSquare_unique_cell κ Λ u row col hk hm hind hq hr a s (congrFun h s))).elim
  · exact h s

omit [StandardBorelSpace P] in
lemma exactSquare_enumeration (hu : Measurable u) (hrow : Measurable row) (hcol : Measurable col)
    (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) :
    Nonempty (BorelFibreEnumeration (exactSquareSet κ Λ u row col)) := by
  let A := exactSquareSet κ Λ u row col
  let : StandardBorelSpace A := (measurableSet_exactSquareSet κ Λ u row col hu hrow hcol).standardBorel
  obtain ⟨i₀⟩ : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨C,_,hcover,_,hemb⟩ := HilbertCode.separated_branches
    (fun t : A => t.1.1) measurable_subtype_coe.fst
    (fun t : A => t.1.2 i₀ i₀)
    ((measurable_pi_apply i₀).comp ((measurable_pi_apply i₀).comp measurable_subtype_coe.snd))
    (by
      intro x y he
      exact ((x.property.1 i₀).1 i₀).trans
        ((congrArg (fun e => u (row e i₀) i₀) he).trans ((y.property.1 i₀).1 i₀).symm))
    1 (by norm_num) (by
      intro x y he hne
      have hy : (x.1.1,y.1.2) ∈ A := by rw [he]; exact y.property
      exact exactSquare_separated κ Λ u row col hk hm hind x.property hy i₀ i₀
        (fun h => hne (Subtype.ext (Prod.ext he h))))
  let d : Q → I → I → HilbertCode κ := fun e a s => HilbertCode.encode (u (row e a) s) 0
  have hd : Measurable d := by
    apply Measurable.of_eval
    intro a
    apply Measurable.of_eval
    intro s
    exact MeasurableSection.zero (((measurable_pi_apply s).comp hu).comp
      ((measurable_pi_apply a).comp hrow))
  obtain ⟨D,sec,hD,hs,_,hmem,hcov⟩ := measurable_branch_sections
    (fun t : A => t.1.1) (fun t => t.1.2) measurable_subtype_coe.snd d hd C hcover hemb
  have hm' (n) (e) (he : e ∈ D n) : (e,sec n e) ∈ A := by
    obtain ⟨t,ht,he⟩ := hmem n e he
    rw [he,←ht]
    exact t.property
  have hc' (e) (q) (hq : (e,q) ∈ A) : ∃ n, e ∈ D n ∧ sec n e = q := hcov ⟨(e,q),hq⟩
  obtain ⟨E,hE,_,he,hec,heu⟩ := enumerate_without_repetition A D sec hD hs hm' hc'
  exact ⟨⟨E,sec,hE,hs,he,hec,heu⟩⟩
end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

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
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    {μ : Measure X} [IsProbabilityMeasure μ] (hμ : M.localLaw.map M.x = μ)
    (hT : MeasurePreserving T μ μ)
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n => μ (A ∩ (T^[n]) ⁻¹' B)) atTop (𝓝 (μ A * μ B)))
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (α : X → A) (hα : Measurable α) (v : A → ℂ)
    (hcenter : ∫ z, v (α z) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => wordEntropy (η := μ) (fun m z => α ((T^[m]) z)) n / n)
      atTop (𝓝 0))
include hM hk hμ hT hmix hα hcenter hH in
lemma saturated_correlation_zero_oai (i : I) (f : I → Arr I M.Y 0 → ℂ)
    (hf : ∀ j, Measurable (f j)) (hb : ∀ j y, ‖f j y‖ ≤ 1)
    (hi : ∀ y, f i y = v (α (M.x (zeroEquiv I M.Y y)))) :
    (∫ y, ∏ j, f j (plane 0 0 j y) ∂M.law 1) = 0 := by
  classical
  obtain ⟨Λ,hΛ,hL,hm,hind⟩ := raw_good_tuple_kernel M (by omega)
  let := hΛ
  obtain ⟨S,hSm,hSb,hSs,hS⟩ := exists_commonLocalLineGraph M hM hk Λ hL hm hind
  obtain ⟨E⟩ := separated_family_enumeration (M.ownKernel 0) S hSm (fun u q hq => (hSb u q hq).1) hSs
  obtain ⟨Eπ⟩ := exactCode_enumeration (M.ownKernel 0) Λ (tupleParameter M)
    (measurable_tupleParameter M) hk hm hind
  obtain ⟨Eσ⟩ := exactSquare_enumeration (M.ownKernel 0) Λ (tupleParameter M)
    (fun e a => plane 1 0 a e) (fun e s => plane 1 (Fin.last 1) s e)
    (measurable_tupleParameter M) (Measurable.of_eval fun _ => measurable_plane _ _ _)
    (Measurable.of_eval fun _ => measurable_plane _ _ _) hk hm hind
  have : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨t,ht⟩ := exists_ne i
  exact raw_correlation_zero M Λ hM hk hL hm hind S hS E Eπ Eσ i t ht.symm
    hμ hT hmix α hα v hcenter hH i f hf hb hi
end ArrayObjects.Object.Rolled

end Rokhlin

end

end OAI
end

theorem solution.{u, u_1} : type_of% @OAI.Rokhlin.ArrayObjects.Object.Rolled.saturated_correlation_zero_oai.{u, u_1} := @OAI.Rokhlin.ArrayObjects.Object.Rolled.saturated_correlation_zero_oai.{u, u_1}
