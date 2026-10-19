-- Prove2me | solution 1 for OAI.C0Absorption.fixed_cylinder_tails_false_aux
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:29:22.647764+00:00
-- url     : https://prove2.me/submissions/38b44858-769b-409f-a0c2-94f8d1a5e563

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Detection.lean:L36-L128
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.fixed_cylinder_tails_false_aux. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations
import Definitions.Def_OAI_Analysis_C0Absorption_Detection
import Theorems.Thm_OAI_C0Absorption_VClass_lipschitz
import Theorems.Thm_OAI_C0Absorption_bounded_signs_weak_null
import Theorems.Thm_OAI_C0Absorption_compatible_detectors_false
import Theorems.Thm_OAI_C0Absorption_completedPairing_add
import Theorems.Thm_OAI_C0Absorption_disjoint_supports_signed_lipschitz
import Theorems.Thm_OAI_C0Absorption_nat_constant_or_tendsto
import Theorems.Thm_OAI_C0Absorption_tail_separation

-- ---- from OAI.Analysis.C0Absorption.Pairings ----
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedPairings

open UniformSpace Completion
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

theorem completedTest_eq (f : S → ℝ) (K : ℝ≥0)
    (h : ∀ m : PreSpace L o, |pairing S f m| ≤ K * ‖m‖) (z : TestSpace L o) :
    completedTest L o f K h z = completedPairing L o f z := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_eq (completedTest L o f K h).continuous Completion.continuous_extension
  | ih m =>
    change (initialPairing L o f K h).extend (toTestSpace L o) (toTestSpace L o m) =
      completedPairing L o f (toTestSpace L o m)
    rw [ContinuousLinearMap.extend_eq _ Completion.denseRange_coe
      (Completion.isUniformInducing_coe (PreSpace L o)), completedPairing_coe L o f K h]
    rfl

end CompletedPairings

section FurtherDetectors

variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

end FurtherDetectors

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Coordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace C0Absorption
noncomputable section

theorem tailFactor_eq_one {c : ℝ} (hc : 0 < c) (N : ℕ) (s : C0) (hs : tau N s ≤ c) :
    tailFactor c N s = 1 := by
  apply min_eq_left
  apply (le_max_left _ _).trans'
  have hdiv := (div_le_one hc).mpr hs
  linarith

theorem remainderTail_support {c : ℝ} (hc : 0 < c) (N : ℕ) :
    tsupport (fun s => tailFactor c N s-1) ⊆ {s | c ≤ tau N s} := by
  apply closure_minimal
  · intro s hs
    by_contra hh
    have he := tailFactor_eq_one hc N s (le_of_not_ge hh)
    exact hs (by simp only [he, sub_self])
  · exact isClosed_le continuous_const (tau_lipschitz N).continuous

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Duality ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

section ClassDuality
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

theorem BoundedTest.weak_null {f : S → ℝ} (hf : BoundedTest L o f)
    (m : ℕ → TestSpace L o) (M : ℝ)
    (hm : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M) :
    Tendsto (fun i => completedPairing L o f (m i)) atTop (nhds 0) := by
  obtain ⟨K,hK⟩ := hf
  simpa only [completedTest_eq] using bounded_signs_weak_null m M hm (completedTest L o f K hK)

end ClassDuality

variable {Γ : Type*} {B : CylinderBases Γ}

theorem VClass_mono {h k : ℕ} (hk : h ≤ k) : VClass B h ⊆ VClass B k := by
  rintro f ⟨γ,r,ts,hr,hj,ht,hs,rfl⟩
  exact ⟨γ,r,ts,hr.trans hk,hj.trans hk,ht.trans hk,fun t hm => (hs t hm).trans hk,rfl⟩

theorem VClass_pairing_bound (B : CylinderBases Γ) (h : ℕ) :
    ∃ A : ℝ≥0, ∀ f ∈ VClass B h, ∀ m : PreSpace (sourceClasses B) c0Origin,
      |pairing C0Ball f m| ≤ A*‖m‖ := by
  have hh := class_pairing_bound (sourceClasses B) c0Origin (2*h+1)
    (4^(h+1)*B.L0+(h+1)*4^(h+1)*B.A) (by
      simpa only [sourceClasses_odd, Nat.cast_add, Nat.cast_one] using (fun f hf => VClass_lipschitz B (h+1) (f := f) hf))
  obtain ⟨A,hA⟩ := hh
  exact ⟨A,fun f hf => hA f (by simpa only [sourceClasses_odd] using VClass_mono (Nat.le_succ h) hf)⟩

theorem VClass_bounded {h : ℕ} {f : C0Ball → ℝ} (hf : f ∈ VClass B h) :
    BoundedTest (sourceClasses B) c0Origin f := by
  obtain ⟨A,hA⟩ := VClass_pairing_bound B h
  exact ⟨A,hA f hf⟩

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

end GeneratedRepresentation
end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Selection ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology

theorem finite_constant_subsequence {A : Type*} [Finite A] (f : ℕ → A) :
    ∃ a, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, f (φ i)=a := by
  have hh : ∃ a, ∃ᶠ i in atTop, f i=a := by
    by_contra hn
    push Not at hn
    have hf : ∀ᶠ i in atTop, ∀ a, f i≠a := Filter.eventually_all.mpr hn
    obtain ⟨i,hi⟩ := hf.exists
    exact hi (f i) rfl
  obtain ⟨a,ha⟩ := hh
  obtain ⟨φ,hm,hp⟩ := extraction_of_frequently_atTop ha
  exact ⟨a,φ,hm,hp⟩

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace TagLocalization
variable {Γ : Type*} {B : CylinderBases Γ} (loc : TagLocalization B)

end TagLocalization

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Operations ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace SignedBound
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m : ℕ → X} {M : ℝ} (hm : SignedBound m M)

include hm

theorem initial : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M :=
  fun n ε => hm n Fin.val Fin.val_injective ε

theorem subsequence {φ : ℕ → ℕ} (hφ : Function.Injective φ) : SignedBound (m ∘ φ) M :=
  fun n ι hι ε => hm n (φ ∘ ι) (hφ.comp hι) ε

end SignedBound

variable {Γ : Type*} {B : CylinderBases Γ}

theorem VClass_compatible_false (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    (F : ℕ → C0Ball → ℝ) (h : ℕ) (K : ℝ≥0) (hF : ∀ i, F i ∈ VClass B h)
    (hLip : ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
      LipschitzWith K (fun s => ∑ i, ε i*F i s))
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m i)|) : False := by
  apply compatible_detectors_false (sourceClasses B) c0Origin m M hm F (2*h+1) K _ hLip hδ hd
  intro i
  simpa only [sourceClasses_odd] using VClass_mono (Nat.le_succ h) (hF i)

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem detection_split (a b : ℕ → ℝ) {δ : ℝ}
    (hd : ∀ i, δ ≤ |a i+b i|) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, δ/2 ≤ |a (φ i)|) ∨
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, δ/2 ≤ |b (φ i)|) := by
  have hh : ∀ i, δ/2 ≤ |a i| ∨ δ/2 ≤ |b i| := by
    intro i
    by_contra hn
    push Not at hn
    have h := (hd i).trans (abs_add_le (a i) (b i))
    linarith [hn.1,hn.2]
  have hf := Filter.frequently_or_distrib.mp (show ∀ᶠ i in atTop, δ/2 ≤ |a i| ∨ δ/2 ≤ |b i| from Filter.Eventually.of_forall hh).frequently
  rcases hf with hf | hf
  · exact Or.inl (extraction_of_frequently_atTop hf)
  · exact Or.inr (extraction_of_frequently_atTop hf)

namespace CylinderOperation
variable {I : Finset ℕ}

end CylinderOperation

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

end GeneratedRepresentation

variable {Γ : Type*} {B : CylinderBases Γ}

theorem VClass_disjoint_false (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    (F : ℕ → C0Ball → ℝ) (h : ℕ) (hF : ∀ i, F i ∈ VClass B h)
    (hdisj : Pairwise (fun i j => Disjoint (tsupport (F i)) (tsupport (F j))))
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m i)|) : False := by
  refine VClass_compatible_false m M hm F h (4^h*B.L0+h*4^h*B.A) hF ?_ hδ hd
  intro n ε hε
  apply disjoint_supports_signed_lipschitz (convex_closedBall (0 : C0) 1)
    (fun i : Fin n => F i) (4^h*B.L0+h*4^h*B.A) (fun i => VClass_lipschitz B h (hF i)) _ ε hε
  intro i j hij
  exact hdisj (show (i : ℕ) ≠ (j : ℕ) from fun he => hij (Fin.ext he))

theorem tail_escape_false (F : ℕ → C0Ball → ℝ) (m : ℕ → SourceSpace B)
    (h : ℕ) (hF : ∀ i, F i ∈ VClass B h) (M : ℝ) (hm : SignedBound m M)
    {δ cstar : ℝ} (hδ : 0 < δ) (hcstar : 0 < cstar)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m i)|)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hs : ∀ i s, s ∈ tsupport (F i) → cstar ≤ tau (N i) s.val) : False := by
  obtain ⟨H,φ,hφ,G,hG,hdG,hdis⟩ := tail_separation F m hF hδ hcstar hd N hN hs
  exact VClass_disjoint_false (m ∘ φ) M (hm.subsequence hφ.injective) G H hG hdis (half_pos hδ) hdG

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace TailOperation
theorem factor_split (t : TailOperation) (ht : t.isBasic=true) (s : C0Ball) :
    t.factor s = 1+t.remainder.factor s := by simp [factor,remainder,ht]

theorem constant_or_escape (t : ℕ → TailOperation) (h : ℕ) (ht : ∀ i, (t i).scaleIndex ≤ h) :
    (∃ p, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, t (φ i)=p) ∨
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ a g,
      (∀ i, (t (φ i)).scaleIndex=a) ∧ (∀ i, (t (φ i)).isBasic=g) ∧
      Tendsto (fun i => (t (φ i)).tailIndex) atTop atTop) := by
  obtain ⟨ag,ψ,hψ,hag⟩ := finite_constant_subsequence
    (fun i => ((⟨(t i).scaleIndex,Nat.lt_succ_of_le (ht i)⟩ : Fin (h+1)),(t i).isBasic))
  have ha (i : ℕ) : (t (ψ i)).scaleIndex=ag.1.val := congrArg (fun p : Fin (h+1) × Bool => p.1.val) (hag i)
  have hg (i : ℕ) : (t (ψ i)).isBasic=ag.2 := congrArg Prod.snd (hag i)
  rcases nat_constant_or_tendsto (fun i => (t (ψ i)).tailIndex) with ⟨N,η,hη,hN⟩ | hN
  · exact Or.inl ⟨⟨ag.1.val,N,ag.2⟩,ψ ∘ η,hψ.comp hη,fun i => ext' (ha _) (hN _) (hg _)⟩
  · exact Or.inr ⟨ψ,hψ,ag.1.val,ag.2,ha,hg,hN⟩
end TailOperation

theorem tailProduct_eq_zero (ts : List TailOperation) (t : TailOperation) (ht : t ∈ ts)
    (s : C0Ball) (hz : t.factor s=0) : tailProduct ts s=0 := by
  unfold tailProduct
  apply List.prod_eq_zero
  exact List.mem_map.mpr ⟨t,ht,hz⟩

theorem full_tail_support (f : C0Ball → ℝ) (ts : List TailOperation) (t : TailOperation)
    (ht : t ∈ ts) (hg : t.isBasic=false) :
    tsupport (fun s => f s*tailProduct ts s) ⊆ {s | dyadic t.scaleIndex ≤ tau (t.tailIndex+1) s.val} := by
  apply closure_minimal
  · intro s hs
    have hn : t.factor s ≠ 0 := by
      intro hz
      exact hs (by change f s*tailProduct ts s=0; rw [tailProduct_eq_zero ts t ht s hz,mul_zero])
    have hh := remainderTail_support (dyadic_pos t.scaleIndex) (t.tailIndex+1)
      (subset_tsupport _ (show tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) s.val-1 ≠ 0 by
        simpa only [TailOperation.factor,hg,Bool.false_eq_true,↓reduceIte] using hn))
    exact hh
  · exact isClosed_le continuous_const ((tau_lipschitz _).continuous.comp continuous_subtype_val)

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Detection ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
variable {Γ : Type*} {B : CylinderBases Γ}

theorem constant_detector_false (f : C0Ball → ℝ) (hf : BoundedTest (sourceClasses B) c0Origin f)
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin f (m i)|) : False := by
  have hh := (hf.weak_null (sourceClasses B) c0Origin m M hm.initial).abs
  have he : ∀ᶠ i in atTop, |completedPairing (sourceClasses B) c0Origin f (m i)| < δ :=
    hh.eventually (show ∀ᶠ x in nhds |(0 : ℝ)|, x<δ by simpa only [abs_zero] using eventually_lt_nhds hδ)
  obtain ⟨i,hi⟩ := he.exists
  exact (not_lt_of_ge (hd i)) hi

theorem tail_remainder_false (f : ℕ → C0Ball → ℝ) (ts : ℕ → List TailOperation)
    (t : ℕ → TailOperation) (ht : ∀ i, t i ∈ ts i) (hg : ∀ i, (t i).isBasic=false)
    (a : ℕ) (ha : ∀ i, (t i).scaleIndex=a) (hN : Tendsto (fun i => (t i).tailIndex) atTop atTop)
    (h : ℕ) (hF : ∀ i, (fun s => f i s*tailProduct (ts i) s) ∈ VClass B h)
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => f i s*tailProduct (ts i) s) (m i)|) : False := by
  apply tail_escape_false (fun i s => f i s*tailProduct (ts i) s) m h hF M hm hδ (dyadic_pos a) hd
    (fun i => (t i).tailIndex+1) (tendsto_atTop_mono (fun i => Nat.le_succ _) hN)
  intro i s hs
  simpa only [ha i,Set.mem_ofPred_eq] using full_tail_support (f i) (ts i) (t i) (ht i) (hg i) hs

theorem fixed_cylinder_tails_false_aux {γ : Γ} (r : GeneratedRepresentation B γ) (h : ℕ)
    (hr : r.operations.length ≤ h) (hj : B.band γ ≤ h) (n : ℕ) :
    ∀ (pre : List TailOperation) (post : ℕ → List TailOperation),
      (∀ i, (post i).length=n) →
      (∀ i, (pre++post i).length ≤ h) →
      (∀ i t, t ∈ pre++post i → t.scaleIndex ≤ h) →
      ∀ (m : ℕ → SourceSpace B) (M : ℝ), SignedBound m M →
      ∀ δ : ℝ, 0 < δ →
      (∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
        (fun s => r.value s*tailProduct (pre++post i) s) (m i)|) → False := by
  induction n with
  | zero =>
    intro pre post hn hlen hscale m M hm δ hδ hd
    have hz (i : ℕ) : post i=[] := List.length_eq_zero_iff.mp (hn i)
    have hmem : (fun s => r.value s*tailProduct pre s) ∈ VClass B h := by
      refine ⟨γ,r,pre,hr,hj,?_,?_,rfl⟩
      · simpa only [hz 0,List.append_nil] using hlen 0
      · intro t ht
        apply hscale 0 t
        exact List.mem_append.mpr (Or.inl ht)
    apply constant_detector_false _ (VClass_bounded hmem) m M hm hδ
    intro i
    simpa only [hz i,List.append_nil] using hd i
  | succ n ih =>
    intro pre post hn hlen hscale m M hm δ hδ hd
    have hc (i : ℕ) : ∃ t rest, post i=t::rest ∧ rest.length=n := by
      obtain ⟨t,rest,he⟩ := List.length_pos_iff_exists_cons.mp (show 0<(post i).length by rw [hn]; omega)
      refine ⟨t,rest,he,?_⟩
      have hh := hn i
      rw [he,List.length_cons] at hh
      omega
    choose t rest he hrest using hc
    have ht (i : ℕ) : t i ∈ pre++post i := List.mem_append.mpr (Or.inr (by rw [he]; exact List.mem_cons_self))
    rcases TailOperation.constant_or_escape t h (fun i => hscale i _ (ht i)) with
      ⟨p,ψ,hψ,hp⟩ | ⟨ψ,hψ,a,g,ha,hg,hN⟩
    · have heq (i : ℕ) : (pre++[p])++rest (ψ i)=pre++post (ψ i) := by
        rw [he,hp,List.append_assoc,List.singleton_append]
      apply ih (pre++[p]) (fun i => rest (ψ i)) (fun i => hrest _) (fun i => by rw [heq]; exact hlen _)
        (fun i t ht => hscale (ψ i) t (by rw [← heq]; exact ht)) (m ∘ ψ) M
        (hm.subsequence hψ.injective) δ hδ
      intro i
      simpa only [heq,Function.comp_def] using hd (ψ i)
    · let ts0 (i : ℕ) := pre++post (ψ i)
      have hmem0 (i : ℕ) : (fun s => r.value s*tailProduct (ts0 i) s) ∈ VClass B h :=
        ⟨γ,r,ts0 i,hr,hj,hlen _,hscale _,rfl⟩
      cases g with
      | false =>
        exact tail_remainder_false (fun _ => r.value) ts0 (t ∘ ψ) (fun i => ht _) hg a ha hN
          h hmem0 (m ∘ ψ) M (hm.subsequence hψ.injective) hδ (fun i => hd (ψ i))
      | true =>
        let tsA (i : ℕ) := pre++rest (ψ i)
        let tsB (i : ℕ) := pre++(t (ψ i)).remainder::rest (ψ i)
        have hlenA (i : ℕ) : (tsA i).length ≤ h := by
          have hh := hlen (ψ i)
          simp only [he,List.length_append,List.length_cons] at hh
          simp only [tsA,List.length_append]
          omega
        have hscaleA (i : ℕ) (q : TailOperation) (hq : q ∈ tsA i) : q.scaleIndex ≤ h := by
          apply hscale (ψ i) q
          rw [he,List.mem_append,List.mem_cons]
          rcases List.mem_append.mp hq with hq | hq
          · exact Or.inl hq
          · exact Or.inr (Or.inr hq)
        have hlenB (i : ℕ) : (tsB i).length ≤ h := by
          simpa only [tsB,he,List.length_append,List.length_cons] using hlen (ψ i)
        have hscaleB (i : ℕ) (q : TailOperation) (hq : q ∈ tsB i) : q.scaleIndex ≤ h := by
          rcases List.mem_append.mp hq with hq | hq
          · exact hscale (ψ i) q (List.mem_append.mpr (Or.inl hq))
          · rcases List.mem_cons.mp hq with rfl | hq
            · exact hscale (ψ i) (t (ψ i)) (ht _)
            · exact hscaleA i q (List.mem_append.mpr (Or.inr hq))
        let FA (i : ℕ) (s : C0Ball) := r.value s*tailProduct (tsA i) s
        let FB (i : ℕ) (s : C0Ball) := r.value s*tailProduct (tsB i) s
        have hmemA (i : ℕ) : FA i ∈ VClass B h := ⟨γ,r,tsA i,hr,hj,hlenA i,hscaleA i,rfl⟩
        have hmemB (i : ℕ) : FB i ∈ VClass B h := ⟨γ,r,tsB i,hr,hj,hlenB i,hscaleB i,rfl⟩
        have hsplit (i : ℕ) : (fun s => r.value s*tailProduct (ts0 i) s)=fun s => FA i s+FB i s := by
          funext s
          simp only [ts0,he,tailProduct_append,tailProduct_cons,FA,FB,tsA,tsB]
          rw [TailOperation.factor_split _ (hg i)]
          ring
        have hdet (i : ℕ) : δ ≤ |completedPairing (sourceClasses B) c0Origin (FA i) (m (ψ i))+
            completedPairing (sourceClasses B) c0Origin (FB i) (m (ψ i))| := by
          rw [← completedPairing_add _ _ _ _ (VClass_bounded (hmemA i)) (VClass_bounded (hmemB i))]
          rw [← hsplit]
          exact hd (ψ i)
        rcases detection_split _ _ hdet with ⟨η,hη,hdA⟩ | ⟨η,hη,hdB⟩
        · exact ih pre (fun i => rest (ψ (η i))) (fun i => hrest _) (fun i => hlenA _)
            (fun i => hscaleA _) (m ∘ ψ ∘ η) M (hm.subsequence (hψ.comp hη).injective)
            (δ/2) (half_pos hδ) hdA
        · apply tail_remainder_false (fun _ => r.value) (tsB ∘ η) (fun i => (t (ψ (η i))).remainder)
            (fun i => List.mem_append.mpr (Or.inr List.mem_cons_self)) (fun _ => rfl) a
            (fun i => ha _) (hN.comp hη.tendsto_atTop) h (fun i => hmemB _)
            (m ∘ ψ ∘ η) M (hm.subsequence (hψ.comp hη).injective) (half_pos hδ) hdB

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
variable {Γ : Type*} {B : CylinderBases Γ}

namespace GeneratedRepresentation

end GeneratedRepresentation

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty


theorem solution : type_of% @_root_.OAI.C0Absorption.fixed_cylinder_tails_false_aux := @_root_.OAI.C0Absorption.fixed_cylinder_tails_false_aux
