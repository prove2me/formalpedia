-- Prove2me | solution 1 for OAI.C0Absorption.repeated_label_false_aux
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:31:37.333258+00:00
-- url     : https://prove2.me/submissions/453f2341-e031-4389-a435-c0605a97dde6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Detection.lean:L162-L258
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.repeated_label_false_aux. The node keeps its source
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
import Theorems.Thm_OAI_C0Absorption_completedPairing_add
import Theorems.Thm_OAI_C0Absorption_fixed_cylinder_tails_false_aux
import Theorems.Thm_OAI_C0Absorption_nat_constant_or_tendsto
import Theorems.Thm_OAI_C0Absorption_small_remainders_false

-- ---- from OAI.Analysis.C0Absorption.Coordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace C0Absorption
noncomputable section

theorem dyadic_tendsto : Tendsto dyadic atTop (nhds 0) := by
  change Tendsto (fun a : ℕ => ((2 : ℝ)^a)⁻¹) atTop (nhds 0)
  simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)

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

theorem subsequence {φ : ℕ → ℕ} (hφ : Function.Injective φ) : SignedBound (m ∘ φ) M :=
  fun n ι hι ε => hm n (φ ∘ ι) (hφ.comp hι) ε

end SignedBound

variable {Γ : Type*} {B : CylinderBases Γ}

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

theorem act_split (op : CylinderOperation I) (hG : op.isG=true) (u : Cube I → ℝ) :
    op.act u = u+op.remainder.act u := by
  rw [remainder_act]
  have he : op.act u = localG op.point op.scale u := by
    unfold act localOp
    rw [hG]
    rfl
  rw [he]
  ext x
  exact localG_eq op.point op.scale u x

theorem finite_scale_fiber (a : ℕ) : Finite {op : CylinderOperation I // op.scaleIndex=a} := by
  apply Finite.of_surjective
    (fun p : OperationGrid I a × Bool => (⟨⟨a,p.1,p.2⟩,rfl⟩ : {op : CylinderOperation I // op.scaleIndex=a}))
  rintro ⟨⟨a',c,g⟩,hh⟩
  change a'=a at hh
  subst a'
  exact ⟨(c,g),rfl⟩

theorem constant_or_small (op : ℕ → CylinderOperation I) :
    (∃ p, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, op (φ i)=p) ∨
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun i => (op (φ i)).scale) atTop (nhds 0) ∧
      ∃ g : Bool, ∀ i, (op (φ i)).isG=g) := by
  rcases nat_constant_or_tendsto (fun i => (op i).scaleIndex) with ⟨a,ψ,hψ,ha⟩ | ha
  · let := finite_scale_fiber (I := I) a
    obtain ⟨p,η,hη,hp⟩ := finite_constant_subsequence
      (fun i => (⟨op (ψ i),ha i⟩ : {p : CylinderOperation I // p.scaleIndex=a}))
    exact Or.inl ⟨p.val,ψ ∘ η,hψ.comp hη,fun i => congrArg Subtype.val (hp i)⟩
  · obtain ⟨g,ψ,hψ,hg⟩ := finite_constant_subsequence (fun i => (op i).isG)
    exact Or.inr ⟨ψ,hψ,(dyadic_tendsto.comp ha).comp hψ.tendsto_atTop,g,hg⟩

end CylinderOperation

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

end GeneratedRepresentation

variable {Γ : Type*} {B : CylinderBases Γ}

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
end TailOperation

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

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem fixed_cylinder_tails_false {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}
    (r : GeneratedRepresentation B γ) (ts : ℕ → List TailOperation) (h : ℕ)
    (hr : r.operations.length ≤ h) (hj : B.band γ ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => r.value s*tailProduct (ts i) s) (m i)|) : False := by
  obtain ⟨n,φ,hφ,hn⟩ := finite_constant_subsequence
    (fun i => (⟨(ts i).length,Nat.lt_succ_of_le (ht i)⟩ : Fin (h+1)))
  apply fixed_cylinder_tails_false_aux r h hr hj n.val [] (ts ∘ φ)
    (fun i => congrArg Fin.val (hn i)) (fun i => ht _) (fun i => ha _)
    (m ∘ φ) M (hm.subsequence hφ.injective) δ hδ (fun i => hd (φ i))

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

theorem repeated_label_false_aux (h : ℕ) (hj : B.band γ ≤ h) (n : ℕ) :
    ∀ (pre : List (CylinderOperation (B.coordinates γ)))
      (post : ℕ → List (CylinderOperation (B.coordinates γ)))
      (r : ℕ → GeneratedRepresentation B γ) (ts : ℕ → List TailOperation),
    (∀ i, (post i).length=n) → (∀ i, (r i).operations=pre++post i) →
    (∀ i, (r i).operations.length ≤ h) →
    (∀ i, (ts i).length ≤ h) → (∀ i t, t ∈ ts i → t.scaleIndex ≤ h) →
    ∀ (m : ℕ → SourceSpace B) (M : ℝ), SignedBound m M →
    ∀ δ : ℝ, 0<δ →
    (∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) → False := by
  induction n with
  | zero =>
    intro pre post r ts hn he hr ht ha m M hm δ hδ hd
    have hz (i : ℕ) : post i=[] := List.length_eq_zero_iff.mp (hn i)
    have hval (i : ℕ) : (r i).value=(r 0).value := by
      simp only [GeneratedRepresentation.value,GeneratedRepresentation.cubeValue,he,hz,List.append_nil]
    apply fixed_cylinder_tails_false (r 0) ts h (hr 0) hj ht ha m M hm hδ
    intro i
    simpa only [hval i] using hd i
  | succ n ih =>
    intro pre post r ts hn he hr ht ha m M hm δ hδ hd
    have hc (i : ℕ) : ∃ t rest, post i=t::rest ∧ rest.length=n := by
      obtain ⟨t,rest,heq⟩ := List.length_pos_iff_exists_cons.mp (show 0<(post i).length by rw [hn]; omega)
      refine ⟨t,rest,heq,?_⟩
      have hh := hn i
      rw [heq,List.length_cons] at hh
      omega
    choose op suf hop hsuf using hc
    have hops (i : ℕ) : (r i).operations=pre++op i::suf i := (he i).trans (congrArg (pre++·) (hop i))
    have hsuflen (i : ℕ) : (suf i).length ≤ h := by
      have hh := hr i
      rw [hops,List.length_append,List.length_cons] at hh
      omega
    have horder (i : ℕ) (t : CylinderOperation (B.coordinates γ)) (ht : t ∈ suf i) : t.scale ≤ (op i).scale := by
      have hh := (r i).ordered
      rw [hops] at hh
      exact (List.pairwise_cons.mp (List.pairwise_append.mp hh).2.1).1 t ht
    rcases CylinderOperation.constant_or_small op with ⟨p,ψ,hψ,hp⟩ | ⟨ψ,hψ,hsmall,g,hg⟩
    · have heq (i : ℕ) : (r (ψ i)).operations=(pre++[p])++suf (ψ i) := by
        rw [hops,hp,List.append_assoc,List.singleton_append]
      exact ih (pre++[p]) (suf ∘ ψ) (r ∘ ψ) (ts ∘ ψ) (fun i => hsuf _) heq
        (fun i => hr _) (fun i => ht _) (fun i => ha _) (m ∘ ψ) M (hm.subsequence hψ.injective) δ hδ (fun i => hd (ψ i))
    · let p : Cube (B.coordinates γ) → ℝ := applyOperations pre (B.base γ)
      have hp : LipschitzWith (4^pre.length*B.L0) p := applyOperations_lipschitz pre (B.base_lipschitz γ)
      cases g with
      | false =>
        apply small_remainders_false (r ∘ ψ) (ts ∘ ψ) h (fun i => hr _) hj (fun i => ht _) (fun i => ha _)
          (op ∘ ψ) hsmall p (4^pre.length*B.L0) hp (suf ∘ ψ) (fun i => hsuflen _) (fun i => horder _) _
          (m ∘ ψ) M (hm.subsequence hψ.injective) hδ (fun i => hd (ψ i))
        intro i
        simp only [Function.comp_def,GeneratedRepresentation.cubeValue,hops,applyOperations_append,applyOperations_cons,p]
        have he' : (op (ψ i)).act p=(op (ψ i)).remainder.act p := by
          simp only [CylinderOperation.act,localOp,hg i,Bool.false_eq_true,↓reduceIte]
          rfl
        exact congrArg (applyOperations (suf (ψ i))) he'
      | true =>
        have hsub (i : ℕ) : (pre++suf (ψ i)).Sublist (r (ψ i)).operations := by
          rw [hops]
          exact (List.sublist_cons_self _ _).append_left pre
        let rA (i : ℕ) := (r (ψ i)).subrepresentation (pre++suf (ψ i)) (hsub i)
        have hsame (i : ℕ) : (pre++(op (ψ i)).remainder::suf (ψ i)).map CylinderOperation.scale =
            (r (ψ i)).operations.map CylinderOperation.scale := by
          simp only [hops,List.map_append,List.map_cons,CylinderOperation.remainder_scale]
        let rB (i : ℕ) := (r (ψ i)).sameScales (pre++(op (ψ i)).remainder::suf (ψ i)) (hsame i)
        have hlenA (i : ℕ) : (rA i).operations.length ≤ h := (hsub i).length_le.trans (hr _)
        have hlenB (i : ℕ) : (rB i).operations.length ≤ h := by
          simpa only [rB,GeneratedRepresentation.sameScales,hops,List.length_append,List.length_cons] using hr (ψ i)
        have hcubeB (i : ℕ) : (rB i).cubeValue=applyOperations (suf (ψ i)) ((op (ψ i)).remainder.act p) := by
          simp only [rB,GeneratedRepresentation.sameScales,GeneratedRepresentation.cubeValue,
            applyOperations_append,applyOperations_cons,p]
        let FA (i : ℕ) (s : C0Ball) := (rA i).value s*tailProduct (ts (ψ i)) s
        let FB (i : ℕ) (s : C0Ball) := (rB i).value s*tailProduct (ts (ψ i)) s
        have hmemA (i : ℕ) : FA i ∈ VClass B h := ⟨γ,rA i,ts (ψ i),hlenA i,hj,ht _,ha _,rfl⟩
        have hmemB (i : ℕ) : FB i ∈ VClass B h := ⟨γ,rB i,ts (ψ i),hlenB i,hj,ht _,ha _,rfl⟩
        have hcube (i : ℕ) : (r (ψ i)).cubeValue=(rA i).cubeValue+(rB i).cubeValue := by
          rw [hcubeB]
          change applyOperations (r (ψ i)).operations (B.base γ)=applyOperations (pre++suf (ψ i)) (B.base γ)+_
          rw [hops,applyOperations_append,applyOperations_cons,applyOperations_append]
          rw [CylinderOperation.act_split _ (hg i),map_add]
        have hsplit (i : ℕ) : (fun s => (r (ψ i)).value s*tailProduct (ts (ψ i)) s)=fun s => FA i s+FB i s := by
          funext s
          simp only [GeneratedRepresentation.value,Function.comp_def,hcube,Pi.add_apply,FA,FB]
          ring
        have hdet (i : ℕ) : δ ≤ |completedPairing (sourceClasses B) c0Origin (FA i) (m (ψ i))+
            completedPairing (sourceClasses B) c0Origin (FB i) (m (ψ i))| := by
          rw [← completedPairing_add _ _ _ _ (VClass_bounded (hmemA i)) (VClass_bounded (hmemB i)),← hsplit]
          exact hd (ψ i)
        rcases detection_split _ _ hdet with ⟨η,hη,hdA⟩ | ⟨η,hη,hdB⟩
        · exact ih pre (suf ∘ ψ ∘ η) (rA ∘ η) (ts ∘ ψ ∘ η) (fun i => hsuf _)
            (fun i => rfl) (fun i => hlenA _) (fun i => ht _) (fun i => ha _)
            (m ∘ ψ ∘ η) M (hm.subsequence (hψ.comp hη).injective) (δ/2) (half_pos hδ) hdA
        · exact small_remainders_false (rB ∘ η) (ts ∘ ψ ∘ η) h (fun i => hlenB _) hj
            (fun i => ht _) (fun i => ha _) (op ∘ ψ ∘ η) (hsmall.comp hη.tendsto_atTop) p
            (4^pre.length*B.L0) hp (suf ∘ ψ ∘ η) (fun i => hsuflen _) (fun i => horder _)
            (fun i => hcubeB _) (m ∘ ψ ∘ η) M (hm.subsequence (hψ.comp hη).injective)
            (half_pos hδ) hdB

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


theorem solution : type_of% @_root_.OAI.C0Absorption.repeated_label_false_aux := @_root_.OAI.C0Absorption.repeated_label_false_aux
