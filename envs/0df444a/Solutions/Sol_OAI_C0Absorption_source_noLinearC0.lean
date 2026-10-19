-- Prove2me | solution 1 for OAI.C0Absorption.source_noLinearC0
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:33:20.08697+00:00
-- url     : https://prove2.me/submissions/34830ee5-3132-42a0-a8c9-c5c0eef3ed79

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Detection.lean:L372-L386
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.source_noLinearC0. The node keeps its source
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
import Theorems.Thm_OAI_C0Absorption_RadiusLocalization_low_bands_disjoint
import Theorems.Thm_OAI_C0Absorption_VClass_lipschitz
import Theorems.Thm_OAI_C0Absorption_compatible_detectors_false
import Theorems.Thm_OAI_C0Absorption_constant_or_injective_subsequence
import Theorems.Thm_OAI_C0Absorption_disjoint_supports_signed_lipschitz
import Theorems.Thm_OAI_C0Absorption_high_bands_compatible
import Theorems.Thm_OAI_C0Absorption_nat_constant_or_tendsto
import Theorems.Thm_OAI_C0Absorption_one_class_detects
import Theorems.Thm_OAI_C0Absorption_repeated_label_false_aux

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

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

theorem repeated_label_false (r : ℕ → GeneratedRepresentation B γ)
    (ts : ℕ → List TailOperation) (h : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h) (hj : B.band γ ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) : False := by
  obtain ⟨n,φ,hφ,hn⟩ := finite_constant_subsequence
    (fun i => (⟨(r i).operations.length,Nat.lt_succ_of_le (hr i)⟩ : Fin (h+1)))
  exact repeated_label_false_aux h hj n.val [] (fun i => (r (φ i)).operations) (r ∘ φ) (ts ∘ φ)
    (fun i => congrArg Fin.val (hn i)) (fun i => rfl) (fun i => hr _) (fun i => ht _) (fun i => ha _)
    (m ∘ φ) M (hm.subsequence hφ.injective) δ hδ (fun i => hd (φ i))

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
variable {Γ : Type*} {B : CylinderBases Γ}

namespace GeneratedRepresentation

end GeneratedRepresentation

theorem bounded_band_detectors_false (loc : RadiusLocalization B)
    (γ : ℕ → Γ) (r : ∀ i, GeneratedRepresentation B (γ i))
    (ts : ℕ → List TailOperation) (h : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h) (hj : ∀ i, B.band (γ i) ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) : False := by
  rcases constant_or_injective_subsequence γ with ⟨γ0,ψ,hψ,hγ⟩ | ⟨ψ,hψ,hγ⟩
  · let rr (i : ℕ) := (r (ψ i)).relabel (hγ i)
    apply repeated_label_false rr (ts ∘ ψ) h (fun i => by simpa only [rr,GeneratedRepresentation.relabel_length] using hr (ψ i))
      (by rw [← hγ 0]; exact hj _) (fun i => ht _) (fun i => ha _) (m ∘ ψ) M
      (hm.subsequence hψ.injective) hδ
    intro i
    simpa only [rr,GeneratedRepresentation.relabel_value,Function.comp_def] using hd (ψ i)
  · obtain ⟨j,η,hη,hjη⟩ := finite_constant_subsequence
      (fun i => (⟨B.band (γ (ψ i)),Nat.lt_succ_of_le (hj _)⟩ : Fin (h+1)))
    obtain ⟨H,φ,hφ,F,hF,hdF,hdis⟩ := loc.low_bands_disjoint (γ ∘ ψ ∘ η) (fun i => r (ψ (η i)))
      (ts ∘ ψ ∘ η) h j.val (fun i => hr _) (fun i => congrArg Fin.val (hjη i))
      (Nat.le_of_lt_succ j.isLt) (fun i => ht _) (fun i => ha _) (hγ.comp hη.injective)
      (m ∘ ψ ∘ η) hδ (fun i => hd (ψ (η i)))
    exact VClass_disjoint_false (m ∘ ψ ∘ η ∘ φ) M (hm.subsequence ((hψ.comp hη).comp hφ).injective)
      F H hF hdis (half_pos hδ) hdF

theorem source_detectors_false (locT : TagLocalization B) (locR : RadiusLocalization B)
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    (F : ℕ → C0Ball → ℝ) (d : ℕ) (hF : ∀ i, F i ∈ sourceClasses B d)
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m i)|) : False := by
  let h := d/2+1
  by_cases hdEven : d%2=0
  · have ht (i : ℕ) : F i ∈ TClass B h := by simpa only [sourceClasses,hdEven,↓reduceIte,h] using hF i
    choose γ r hr he using ht
    have hdet (i : ℕ) : δ ≤ |completedPairing (sourceClasses B) c0Origin (r i).value (m i)| := by
      simpa only [he i] using hd i
    rcases nat_constant_or_tendsto (fun i => B.band (γ i)) with ⟨j,ψ,hψ,hj⟩ | hj
    · apply bounded_band_detectors_false locR (γ ∘ ψ) (fun i => r (ψ i)) (fun _ => []) (h+j)
        (fun i => (hr _).trans (Nat.le_add_right h j)) (fun i => by change B.band (γ (ψ i)) ≤ h+j; rw [hj]; omega)
        (by simp) (by simp) (m ∘ ψ) M (hm.subsequence hψ.injective) hδ
      intro i
      simpa only [tailProduct_nil,mul_one,Function.comp_def] using hdet (ψ i)
    · obtain ⟨φ,hφ,G,hG,hdG,hLip⟩ := high_bands_compatible locT γ r h hr hj m hδ hdet
      apply compatible_detectors_false (sourceClasses B) c0Origin (m ∘ φ) M (hm.subsequence hφ.injective)
        G (2*h) (4^(h+1)*B.L0+1) _ hLip (half_pos hδ) hdG
      intro i
      simpa only [sourceClasses_even] using hG i
  · have ht (i : ℕ) : F i ∈ VClass B h := by simpa only [sourceClasses,hdEven,↓reduceIte,h] using hF i
    choose γ r ts hr hj hts ha he using ht
    apply bounded_band_detectors_false locR γ r ts h hr hj hts ha m M hm hδ
    intro i
    simpa only [he i] using hd i

theorem source_no_bounded_signs_lower (locT : TagLocalization B) (locR : RadiusLocalization B)
    (m : ℕ → SourceSpace B) (M r : ℝ) (hm : SignedBound m M) (hr : 0 < r)
    (hlower : ∀ i, r ≤ ‖m i‖) : False := by
  obtain ⟨h,δ,hδ,φ,hφ,F,hF⟩ := one_class_detects (sourceClasses B) c0Origin m M r hr hlower hm.initial
  exact source_detectors_false locT locR (m ∘ φ) M (hm.subsequence hφ.injective) F h
    (fun i => (hF i).1) hδ (fun i => (hF i).2)

theorem atoms_signed_bound : SignedBound atom 1 := by
  classical
  intro n ι hι ε
  apply c0_norm_le _ zero_le_one
  intro k
  change |c0Eval k (∑ i, realSign (ε i) • atom (ι i))| ≤ 1
  simp only [map_sum,map_smul,smul_eq_mul,c0Eval_apply,atom_apply]
  by_cases hex : ∃ i, ι i=k
  · obtain ⟨i,hi⟩ := hex
    rw [Finset.sum_eq_single i]
    · simpa only [hi,ite_true,mul_one] using (abs_realSign (ε i)).le
    · intro j hj hji
      have hneq : ι j≠k := by intro he; exact hji (hι (he.trans hi.symm))
      simp only [hneq,ite_false,mul_zero]
    · simp
  · push Not at hex
    simp only [hex,ite_false,mul_zero,Finset.sum_const_zero,abs_zero,zero_le_one]

theorem source_noLinearC0 (locT : TagLocalization B) (locR : RadiusLocalization B) :
    NoLinearC0 (SourceSpace B) := by
  intro T hT
  obtain ⟨c,hc,hcT⟩ := hT
  let m (i : ℕ) := T (atom i)
  have hm : SignedBound m ‖T‖ := by
    intro n ι hι ε
    change ‖∑ i, realSign (ε i) • T (atom (ι i))‖ ≤ ‖T‖
    rw [show (∑ i, realSign (ε i) • T (atom (ι i))) = T (∑ i, realSign (ε i) • atom (ι i)) by simp only [map_sum,map_smul]]
    calc
      _ ≤ ‖T‖ * ‖∑ i, realSign (ε i) • atom (ι i)‖ := T.le_opNorm _
      _ ≤ ‖T‖*1 := mul_le_mul_of_nonneg_left (atoms_signed_bound n ι hι ε) (ContinuousLinearMap.opNorm_nonneg T)
      _ = ‖T‖ := mul_one _
  exact source_no_bounded_signs_lower locT locR m ‖T‖ c hm hc
    (fun i => by simpa only [atom_norm,mul_one] using hcT (atom i))

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


theorem solution : type_of% @_root_.OAI.C0Absorption.source_noLinearC0 := @_root_.OAI.C0Absorption.source_noLinearC0
