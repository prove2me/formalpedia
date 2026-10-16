-- Prove2me | solution 1 for OAI.PartialPermutation.complementaryCosets_finite
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:47:19.554027+00:00
-- url     : https://prove2.me/submissions/c00793d3-6269-4a2e-8e6d-c7c10e6e0861

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/Main.lean:L11-L51
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.PartialPermutation.complementaryCosets_finite.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_PartialPermutation_complementaryCosets_finite) verbatim and is proved by it.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SmallKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ProjectionCovers
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Restriction
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicMatrices
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Equivalences
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SymmetricTransfer
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_StandardTableaux
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RankFillings
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagonalBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_FillingExtensions
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Interleavings
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RowBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Truncation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TailBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagramCounts
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DeficitCounts
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TableauWeights
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Tabloids
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ColumnSorting
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_AlternatingTabloids
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Polytabloids
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SpechtModules
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ColumnRearrangement
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TableauVectors
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CrossTableaux
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SpechtShapes
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConjugacyCounts
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ClassCharacters
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SpechtClassification
import Theorems.Thm_OAI_PartialPermutation_TableauZeta_deficitTerm_bound
import Theorems.Thm_OAI_PartialPermutation_TableauZeta_summable_majorant
import Theorems.Thm_OAI_PartialPermutation_Tableau_fixed_deficit_growth
import Theorems.Thm_OAI_PartialPermutation_small_degree_sum_transfer

-- ---- from OAI.RepresentationTheory.PartialPermutation.HilbertSchmidt ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate

namespace PartialPermutation
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]

lemma hsNormSq_eq_sum {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ V)
    (A : Module.End ℂ V) : hsNormSq A = ∑ i, ‖A (e i)‖ ^ 2 := by
  rw [hsNormSq, LinearMap.trace_eq_sum_inner _ e, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.End.mul_apply, LinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (A (e i))

lemma hsNormSq_nonneg (A : Module.End ℂ V) : 0 ≤ hsNormSq A := by
  rw [hsNormSq_eq_sum (stdOrthonormalBasis ℂ V)]
  positivity

lemma hsNormSq_adjoint (A : Module.End ℂ V) : hsNormSq (LinearMap.adjoint A) = hsNormSq A := by
  unfold hsNormSq
  rw [LinearMap.adjoint_adjoint, LinearMap.trace_mul_comm]

end
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.BlockSubgroups ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped MonoidAlgebra BigOperators
open scoped BigOperators

namespace PartialPermutation

lemma blockSubgroup_commute {X : Type*} {M N : Set X} (h : Disjoint M N)
    {g k : Equiv.Perm X} (hg : g ∈ blockSubgroup M) (hk : k ∈ blockSubgroup N) :
    Commute g k := by
  apply Equiv.Perm.Disjoint.commute
  intro x
  by_cases hx : x ∈ M
  · right
    exact hk x (fun hn => Set.disjoint_left.mp h hx hn)
  · exact Or.inl (hg x hx)

end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.ReciprocalTransfer ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped MonoidAlgebra BigOperators
open scoped BigOperators

namespace PartialPermutation
noncomputable section

lemma inverseDegreeSum_nonneg (G : Type*) [Group G] [Fintype G] (u : ℝ) :
    0 ≤ inverseDegreeSum G u := by
  exact Finset.sum_nonneg (fun c _ => Real.rpow_nonneg (by positivity) _)

lemma smallDegreeSum_le_inverseDegreeSum (G : Type*) [Group G] [Fintype G]
    {u R : ℝ} (hu : 0 < u) (hR : 0 < R) :
    smallDegreeSum G R ≤ R^(u+2) * inverseDegreeSum G u := by
  rw [smallDegreeSum, inverseDegreeSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  split_ifs with hc
  · have hd : 0 < (irreducibleDegree c : ℝ) := by
      have : Nontrivial (irreducibleSpace c) :=
        IsSimpleModule.nontrivial ℂ[G] (irreducibleRep c).asModule
      exact_mod_cast (Module.finrank_pos : 0 < irreducibleDegree c)
    calc
      (irreducibleDegree c : ℝ)^2 =
          (irreducibleDegree c : ℝ)^(u+2) * (irreducibleDegree c : ℝ)^(-u) := by
        rw [← Real.rpow_add hd]
        ring_nf
        rw [Real.rpow_two]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hd.le hc (by linarith)) (Real.rpow_nonneg hd.le _)
  · positivity

variable {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) {b : ℕ} (H : Fin b → Subgroup G)

theorem inverse_degree_sum_transfer [Representation.IsIrreducible ρ]
    (hb : 0 < b) (hρ : IsUnitary ρ)
    (hcomm : ∀ i j, i ≠ j → ∀ g ∈ H i, ∀ k ∈ H j, Commute g k)
    (f : G → ℝ) (B u : ℝ) (hf : ∀ g, 0 ≤ f g) (hu : 0 < u)
    (hcap : ∀ i, LeftCosetCap f (H i) B) :
    hsNormSq (complexFourier ρ (fun g => f g)) ≤
      B * mass f * (Module.finrank ℂ V : ℝ)^(-1 + (u+2)/(b : ℝ)) *
        ∑ i, inverseDegreeSum (H i) u := by
  have : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  have hD : 0 < (Module.finrank ℂ V : ℝ) := by exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℂ V)
  have hB : 0 ≤ B := by
    let i : Fin b := ⟨0, hb⟩
    have hp : (0 : ℝ) < (H i).index := by
      exact_mod_cast Nat.pos_of_ne_zero (H i).index_ne_zero_of_finite
    have hz : 0 ≤ B / (H i).index :=
      (Finset.sum_nonneg (fun (g : H i) _ => hf (1*g))).trans (hcap i 1)
    simpa only [div_mul_cancel₀ B hp.ne'] using mul_nonneg hz hp.le
  have hm : 0 ≤ mass f := Finset.sum_nonneg (fun g _ => hf g)
  have ht := small_degree_sum_transfer ρ H hb hρ hcomm f B hf hcap
  have hs : ∑ i, smallDegreeSum (H i) ((Module.finrank ℂ V : ℝ)^(1 / (b : ℝ))) ≤
      (Module.finrank ℂ V : ℝ)^((u+2)/(b : ℝ)) * ∑ i, inverseDegreeSum (H i) u := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have ht := smallDegreeSum_le_inverseDegreeSum (H i) hu (Real.rpow_pos_of_pos hD (1/(b : ℝ)))
    rw [← Real.rpow_mul hD.le] at ht
    convert ht using 1; congr 2; ring
  have hn := ht.trans (mul_le_mul_of_nonneg_left hs (mul_nonneg hB hm))
  apply (mul_le_mul_iff_right₀ hD).mp
  calc
    _ ≤ _ := hn
    _ = _ := by
      rw [show (u+2)/(b : ℝ) = (-1+(u+2)/(b : ℝ))+1 by ring,
        Real.rpow_add hD, Real.rpow_one]
      ring_nf

end
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.Equivalences ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped MonoidAlgebra BigOperators
open scoped BigOperators

namespace PartialPermutation
noncomputable section
variable {G K V W : Type*} [Group G] [Group K]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

variable [Fintype G] [Fintype K]

lemma irreducibleDegree_map (e : G ≃* K) (c : IrreducibleIndex G) :
    irreducibleDegree (irreducibleIndexMap e c) = irreducibleDegree c := by
  obtain ⟨a⟩ := irreducibleIndexMap_spec e c
  exact a.toLinearEquiv.finrank_eq

lemma inverseDegreeSum_equiv (e : G ≃* K) (u : ℝ) :
    inverseDegreeSum G u = inverseDegreeSum K u := by
  apply Fintype.sum_equiv (irreducibleIndexEquiv e)
  intro c
  change (irreducibleDegree c : ℝ)^(-u) = (irreducibleDegree (irreducibleIndexMap e c) : ℝ)^(-u)
  rw [irreducibleDegree_map]

end
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.SymmetricTransfer ----
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped MonoidAlgebra BigOperators
open scoped BigOperators

namespace PartialPermutation
noncomputable section

lemma inverseDegreeSum_block {X : Type*} [Fintype X] [DecidableEq X] (M : Set X) (u : ℝ) :
    inverseDegreeSum (blockSubgroup M) u =
      inverseDegreeSum (Equiv.Perm (Fin (Fintype.card M))) u :=
  inverseDegreeSum_equiv (blockSubgroupSnEquiv M) u

lemma inverseDegreeSum_block_sum {X I : Type*} [Fintype X] [DecidableEq X] [Fintype I]
    (M : I → Set X) (u : ℝ) :
    (∑ i, inverseDegreeSum (blockSubgroup (M i)) u) =
      ∑ i, symmetricInverseDegreeSum (Fintype.card (M i)) u := by
  apply Finset.sum_congr rfl
  intro i _
  exact inverseDegreeSum_block (M i) u

end
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.StandardTableaux ----
namespace OAI

section
namespace PartialPermutation
namespace Tableau

noncomputable section
open Finset

lemma standardCount_pos (μ : YoungDiagram) : 0 < standardCount μ := by
  let : Nonempty (StandardFilling μ.cells) := ⟨chosenFilling _⟩
  exact Fintype.card_pos

end
end Tableau
end PartialPermutation
end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.DeficitCounts ----
namespace OAI

section
namespace PartialPermutation
namespace DiagramCounting
noncomputable section
open Finset

lemma eq_of_dropTop_row (μ ν : YoungDiagram) (hd : dropTop μ=dropTop ν)
    (hr : μ.rowLen 0=ν.rowLen 0) : μ=ν := by
  apply YoungDiagram.ext
  apply Finset.ext
  rintro ⟨i,j⟩
  cases i with
  | zero => exact μ.mem_iff_lt_rowLen.trans (hr ▸ ν.mem_iff_lt_rowLen.symm)
  | succ i =>
    change (i+1,j) ∈ μ ↔ (i+1,j) ∈ ν
    rw [← mem_dropTop μ, ← mem_dropTop ν,hd]

lemma deficitCode_injective (n k : ℕ) : Function.Injective (deficitCode n k) := by
  intro μ ν he
  unfold deficitCode at he
  split_ifs at he with hμ hν hν
  · have hd : dropTop μ.1.1=dropTop ν.1.1 := congrArg (fun t : Bool × Shape k => t.2.1) he
    have hcμ := μ.2
    have hcν := ν.2
    rw [μ.1.2,max_eq_left hμ] at hcμ
    rw [ν.1.2,max_eq_left hν] at hcν
    have hleμ := rowLen_le_card μ.1.1 0
    have hleν := rowLen_le_card ν.1.1 0
    rw [μ.1.2] at hleμ
    rw [ν.1.2] at hleν
    apply Subtype.ext; apply Subtype.ext
    exact eq_of_dropTop_row _ _ hd (by omega)
  · have hh := congrArg Prod.fst he; cases hh
  · have hh := congrArg Prod.fst he; cases hh
  · have hd : dropTop μ.1.1.transpose=dropTop ν.1.1.transpose :=
      congrArg (fun t : Bool × Shape k => t.2.1) he
    have hcμ := μ.2
    have hcν := ν.2
    rw [μ.1.2,max_eq_right (le_of_not_ge hμ)] at hcμ
    rw [ν.1.2,max_eq_right (le_of_not_ge hν)] at hcν
    have hleμ := colLen_le_card μ.1.1 0
    have hleν := colLen_le_card ν.1.1 0
    rw [μ.1.2] at hleμ
    rw [ν.1.2] at hleν
    have htr := eq_of_dropTop_row _ _ hd (by
      simp only [YoungDiagram.rowLen_transpose]; omega)
    apply Subtype.ext; apply Subtype.ext
    have hh := congrArg YoungDiagram.transpose htr
    simpa only [YoungDiagram.transpose_transpose] using hh

lemma deficit_count_le (n k : ℕ) : Fintype.card (ShapeDeficit n k) ≤ 2*partitionCount k := by
  simpa only [Fintype.card_prod,Fintype.card_bool,partitionCount] using
    Fintype.card_le_of_injective (deficitCode n k) (deficitCode_injective n k)

end
end DiagramCounting
end PartialPermutation
end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.TableauWeights ----
namespace OAI

section
namespace PartialPermutation
namespace TableauZeta
noncomputable section
open Finset Filter
open Tableau DiagramCounting

lemma inverseWeight_nonneg (u : ℝ) (μ : YoungDiagram) : 0 ≤ inverseWeight u μ := by
  unfold inverseWeight
  split_ifs <;> positivity

lemma deficitTerm_nonneg (n : ℕ) (u : ℝ) (k : ℕ) : 0 ≤ deficitTerm n u k :=
  Finset.sum_nonneg (fun μ _ => inverseWeight_nonneg u μ.1.1)

end
end TableauZeta
end PartialPermutation
end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.TableauLimits ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

section
namespace PartialPermutation
namespace TableauZeta
noncomputable section
open Finset Filter
open Tableau DiagramCounting

lemma deficitTerm_zero (n : ℕ) (u : ℝ) : deficitTerm n u 0=0 := by
  apply Finset.sum_eq_zero
  intro μ _
  unfold inverseWeight
  have he : deficit μ.1.1=0 := μ.2
  simp only [he,ite_true]

lemma deficitTerm_fixed_bound (n : ℕ) (u : ℝ) (hu : 0 < u) (k : ℕ) (hk : 0 < k)
    (hkn : 2*k≤n) :
    deficitTerm n u k ≤ 2*(partitionCount k:ℝ)*((n-2*k+1:ℕ):ℝ)^(-u) := by
  have hcard : (Fintype.card (ShapeDeficit n k):ℝ) ≤ 2*partitionCount k := by
    exact_mod_cast deficit_count_le n k
  calc
    deficitTerm n u k ≤ ∑ μ : ShapeDeficit n k, ((n-2*k+1:ℕ):ℝ)^(-u) := by
      apply Finset.sum_le_sum
      intro μ _
      have hdef : deficit μ.1.1=k := μ.2
      have hsize : μ.1.1.cells.card=n := μ.1.2
      have hcount := fixed_deficit_growth μ.1.1 (by simpa only [hdef] using hk) (by simpa only [hdef,hsize] using hkn)
      rw [hdef,hsize] at hcount
      unfold inverseWeight
      rw [ite_eq_right (by omega)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity)
        (by exact_mod_cast hcount) (neg_nonpos.mpr hu.le)
    _ = (Fintype.card (ShapeDeficit n k):ℝ)*((n-2*k+1:ℕ):ℝ)^(-u) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (by positivity) _)

lemma deficitTerm_tendsto_zero (u : ℝ) (hu : 0 < u) (k : ℕ) :
    Tendsto (fun n => deficitTerm n u k) atTop (nhds 0) := by
  by_cases hk : k=0
  · subst k
    simpa only [deficitTerm_zero] using tendsto_const_nhds (x := (0:ℝ))
  · have ht : Tendsto (fun n : ℕ => n-2*k+1) atTop atTop := by
      apply tendsto_atTop.2
      intro b
      filter_upwards [eventually_ge_atTop (b+2*k)] with n hn
      omega
    have hr := (tendsto_rpow_neg_atTop hu).comp (tendsto_natCast_atTop_atTop.comp ht)
    have hr' := hr.const_mul (2*(partitionCount k:ℝ))
    simp only [mul_zero] at hr'
    apply squeeze_zero' (Eventually.of_forall (fun n => deficitTerm_nonneg n u k)) _ hr'
    filter_upwards [eventually_ge_atTop (2*k)] with n hn
    exact deficitTerm_fixed_bound n u hu k (by omega) hn

lemma tsum_deficitTerm (n : ℕ) (u : ℝ) :
    (∑' k, deficitTerm n u k) = nontrivialSum n u := by
  have hh := (hasSum_fintype (fun μ : Shape n => inverseWeight u μ.1)).tsum_fiberwise
    (fun μ : Shape n => deficit μ.1)
  change HasSum (fun k => ∑' μ : ShapeDeficit n k, inverseWeight u μ.1.1)
    (nontrivialSum n u) at hh
  simpa only [tsum_fintype,deficitTerm] using hh.tsum_eq

theorem nontrivialSum_tendsto_zero (u : ℝ) (hu : 0 < u) :
    Tendsto (fun n => nontrivialSum n u) atTop (nhds 0) := by
  have hh := tendsto_tsum_of_dominated_convergence (summable_majorant u hu)
    (deficitTerm_tendsto_zero u hu)
    (Eventually.of_forall (fun n k => deficitTerm_bound n u hu k))
  simpa only [tsum_deficitTerm,tsum_zero] using hh

lemma fullSum_bound (n : ℕ) (u : ℝ) (hu : 0 < u) :
    fullSum n u ≤ 2*partitionCount 0 + nontrivialSum n u := by
  have hi (μ : YoungDiagram) : (standardCount μ:ℝ)^(-u) ≤ 1 := by
    have hc : (1:ℝ) ≤ standardCount μ := by exact_mod_cast standardCount_pos μ
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow_of_nonpos (by norm_num) hc (neg_nonpos.mpr hu.le)
  have hc : (Fintype.card (ShapeDeficit n 0):ℝ) ≤ 2*partitionCount 0 := by
    exact_mod_cast deficit_count_le n 0
  calc
    fullSum n u ≤ ∑ μ : Shape n,
        ((if deficit μ.1=0 then (1:ℝ) else 0) + inverseWeight u μ.1) := by
      apply Finset.sum_le_sum
      intro μ _
      unfold inverseWeight
      split_ifs
      · simpa only [add_zero] using hi μ.1
      · simp only [zero_add,le_refl]
    _ = (Fintype.card (ShapeDeficit n 0):ℝ) + nontrivialSum n u := by
      rw [Finset.sum_add_distrib]
      congr 1
      change (∑ μ : Shape n, if deficit μ.1=0 then (1:ℝ) else 0) =
        (Fintype.card {μ : Shape n // deficit μ.1=0}:ℝ)
      rw [Fintype.card_subtype,Finset.sum_boole]
    _ ≤ _ := add_le_add_left hc _

theorem fullSum_bddAbove (u : ℝ) (hu : 0 < u) :
    BddAbove (Set.range (fun n => fullSum n u)) := by
  obtain ⟨a,ha⟩ := (nontrivialSum_tendsto_zero u hu).bddAbove_range
  refine ⟨2*partitionCount 0+a,?_⟩
  rintro x ⟨n,rfl⟩
  exact (fullSum_bound n u hu).trans (add_le_add_right (ha (Set.mem_range_self n)) _)

end
end TableauZeta
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.ColumnRearrangement ----
namespace OAI

section
namespace PartialPermutation.YoungTabloid
noncomputable section
open Finset
open scoped Classical

lemma cell_eq_of_row_col (μ : YoungDiagram) {x y : μ.cells}
    (hr : row μ x=row μ y) (hc : col μ x=col μ y) : x=y :=
  Subtype.ext (Prod.ext hr hc)

lemma cell_lt_of_column (μ : YoungDiagram) {x y : μ.cells}
    (hc : col μ x=col μ y) (hr : row μ x<row μ y) : x<y := by
  apply lt_of_le_of_ne
  · exact ⟨hr.le,hc.le⟩
  · intro h
    exact hr.ne (congrArg (row μ) h)

lemma column_monovary (μ : YoungDiagram) (f : μ.cells → ℕ) (hf : StrictMono f) (j : ℕ) :
    Monovary (fun x : Col μ j => f x.1) (fun x => row μ x.1) := by
  intro x y h
  exact (hf (cell_lt_of_column μ (x.2.trans y.2.symm) h)).le

lemma column_rearrangement (μ : YoungDiagram) (f : μ.cells → ℕ) (hf : StrictMono f)
    (c : columnGroup μ) (j : ℕ) :
    (∑ x : Col μ j, f x.1 * row μ (c.1 x.1)) ≤ ∑ x : Col μ j, f x.1 * row μ x.1 :=
  (column_monovary μ f hf j).sum_mul_comp_perm_le_sum_mul (σ := columnRestrict μ c j)

lemma fin_perm_mono_eq (n : ℕ) (p : Equiv.Perm (Fin n)) (hp : StrictMono p) : p=1 := by
  have hle (i : Fin n) : i.val≤(p i).val := strictMono_fin_nat_le _
    (fun i j h => hp h) i
  have heq : (∑ i : Fin n, i.val)=∑ i : Fin n, (p i).val := (Equiv.sum_comp p Fin.val).symm
  have hh := (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp heq
  apply Equiv.ext
  intro i
  exact Fin.ext (hh i (mem_univ _)).symm

lemma column_rearrangement_eq (μ : YoungDiagram) (f : μ.cells → ℕ) (hf : StrictMono f)
    (c : columnGroup μ) (j : ℕ)
    (he : (∑ x : Col μ j, f x.1 * row μ (c.1 x.1)) = ∑ x : Col μ j, f x.1 * row μ x.1) :
    ∀ x : Col μ j, c.1 x.1=x.1 := by
  have hm := (column_monovary μ f hf j).sum_mul_comp_perm_eq_sum_mul_iff
    (σ := columnRestrict μ c j) |>.mp he
  let e := columnEquiv μ j
  let p := e.symm.trans ((columnRestrict μ c j).trans e)
  have hp : StrictMono p := by
    intro i k hik
    let x := e.symm i
    let y := e.symm k
    have hxy : f x.1 < f y.1 := hf (cell_lt_of_column μ (x.2.trans y.2.symm) hik)
    change row μ (c.1 x.1) < row μ (c.1 y.1)
    by_contra h
    have hr : row μ (c.1 y.1) < row μ (c.1 x.1) := by
      apply lt_of_le_of_ne (Nat.le_of_not_gt h)
      intro hh
      have heq := c.1.injective (cell_eq_of_row_col μ hh
        ((c.2 y.1).trans ((y.2.trans x.2.symm).trans (c.2 x.1).symm)))
      exact hxy.ne (congrArg f heq.symm)
    exact (not_le_of_gt hxy) (hm hr)
  have hp1 := fin_perm_mono_eq _ p hp
  intro x
  have hx := Equiv.congr_fun hp1 (e x)
  change e (columnRestrict μ c j (e.symm (e x)))=e x at hx
  erw [Equiv.symm_apply_apply] at hx
  exact congrArg Subtype.val (e.injective hx)

lemma sum_columns (μ : YoungDiagram) (f : μ.cells → ℕ) :
    (∑ x, f x)=∑ j : Fin (μ.rowLen 0), ∑ x : Col μ j, f x.1 := by
  exact (Fintype.sum_equiv (columnDecomp μ) _
    (fun x : Σ j : Fin (μ.rowLen 0), Col μ j => f x.2.1) (fun _ => rfl)).trans
    (Fintype.sum_sigma _)

lemma full_rearrangement (μ : YoungDiagram) (f : μ.cells → ℕ) (hf : StrictMono f)
    (c : columnGroup μ) :
    (∑ x, f x * row μ (c.1 x)) ≤ ∑ x, f x * row μ x := by
  rw [sum_columns, sum_columns]
  exact Finset.sum_le_sum (fun j _ => column_rearrangement μ f hf c j)

lemma full_rearrangement_eq (μ : YoungDiagram) (f : μ.cells → ℕ) (hf : StrictMono f)
    (c : columnGroup μ) (he : (∑ x, f x * row μ (c.1 x)) = ∑ x, f x * row μ x) : c=1 := by
  rw [sum_columns, sum_columns] at he
  have hh := (Finset.sum_eq_sum_iff_of_le
    (fun (j : Fin (μ.rowLen 0)) _ => column_rearrangement μ f hf c j)).mp he
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact column_rearrangement_eq μ f hf c (colIndex μ x)
    (hh (colIndex μ x) (mem_univ _)) ⟨x,rfl⟩

end
end PartialPermutation.YoungTabloid
end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.TableauVectors ----
namespace OAI

section
namespace PartialPermutation.YoungTabloid
noncomputable section
open Finset
open scoped Classical

lemma rowCell_strictMono (μ : YoungDiagram) (i : ℕ) : StrictMono (rowCell μ i) := by
  intro j k h
  apply lt_of_le_of_ne
  · exact ⟨le_refl _,h.le⟩
  · intro he
    exact h.ne (Fin.ext (congrArg (fun x : μ.cells => x.1.2) he))

lemma standard_eq_of_inverse_rows (μ : YoungDiagram) (s t : Std μ)
    (h : ∀ k, row μ (s.1.symm k)=row μ (t.1.symm k)) : s=t := by
  have hh (i : ℕ) : (fun j => s.1 (rowCell μ i j))=(fun j => t.1 (rowCell μ i j)) := by
    apply ((s.2.comp (rowCell_strictMono μ i)).range_inj
      (t.2.comp (rowCell_strictMono μ i))).mp
    ext k
    constructor
    · rintro ⟨j,rfl⟩
      let x := t.1.symm (s.1 (rowCell μ i j))
      have hx : row μ x=i := by simpa [x,rowCell,row] using (h (s.1 (rowCell μ i j))).symm
      refine ⟨⟨col μ x,?_⟩,?_⟩
      · have hc := μ.mem_iff_lt_rowLen.mp x.2
        simpa only [← hx,row,col] using hc
      · have he : rowCell μ i ⟨col μ x,by simpa only [← hx,row,col] using μ.mem_iff_lt_rowLen.mp x.2⟩=x :=
          cell_eq_of_row_col μ hx.symm rfl
        simp only [Function.comp_apply]
        rw [he]
        exact t.1.apply_symm_apply _
    · rintro ⟨j,rfl⟩
      let x := s.1.symm (t.1 (rowCell μ i j))
      have hx : row μ x=i := by simpa [x,rowCell,row] using h (t.1 (rowCell μ i j))
      refine ⟨⟨col μ x,?_⟩,?_⟩
      · have hc := μ.mem_iff_lt_rowLen.mp x.2
        simpa only [← hx,row,col] using hc
      · have he : rowCell μ i ⟨col μ x,by simpa only [← hx,row,col] using μ.mem_iff_lt_rowLen.mp x.2⟩=x :=
          cell_eq_of_row_col μ hx.symm rfl
        simp only [Function.comp_apply]
        rw [he]
        exact s.1.apply_symm_apply _
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact congrFun (hh (row μ x)) ⟨col μ x,μ.mem_iff_lt_rowLen.mp x.2⟩

lemma tableauTabloid_injective (μ : YoungDiagram) : Function.Injective (tableauTabloid μ) := by
  intro s t h
  apply standard_eq_of_inverse_rows μ s t
  intro k
  have hh := congrFun (congrArg Subtype.val h) ((referenceLabels μ).symm k)
  simpa [tableauTabloid,tableauPerm,relabel,canonical,ofPerm] using hh

lemma score_relabel (μ : YoungDiagram) (g : Equiv.Perm μ.cells) (r : Tabloid μ) :
    score μ (relabel μ g r) = ∑ x, ((referenceLabels μ) (g x)).val * r.1 x := by
  unfold score
  exact (Fintype.sum_equiv g _ _ (fun x => by simp only [relabel_apply,
    Equiv.Perm.inv_def,Equiv.symm_apply_apply])).symm

lemma score_tableau_column (μ : YoungDiagram) (t : Std μ) (c : columnGroup μ) :
    score μ (relabel μ (tableauPerm μ t) (relabel μ c (canonical μ))) =
      ∑ x, (t.1 x).val * row μ (c.1⁻¹ x) := by
  rw [score_relabel]
  apply Finset.sum_congr rfl
  intro x _
  simp [tableauPerm,relabel,canonical,ofPerm]

lemma score_tableau (μ : YoungDiagram) (t : Std μ) :
    score μ (tableauTabloid μ t)=∑ x, (t.1 x).val * row μ x := by
  simpa only [relabel_one,Subgroup.coe_one,inv_one,Equiv.Perm.one_apply,tableauTabloid]
    using score_tableau_column μ t 1

lemma score_column_le (μ : YoungDiagram) (t : Std μ) (c : columnGroup μ) :
    score μ (relabel μ (tableauPerm μ t) (relabel μ c (canonical μ))) ≤
      score μ (tableauTabloid μ t) := by
  rw [score_tableau_column,score_tableau]
  exact full_rearrangement μ _ (fun x y h => t.2 h) c⁻¹

lemma score_column_eq (μ : YoungDiagram) (t : Std μ) (c : columnGroup μ)
    (h : score μ (relabel μ (tableauPerm μ t) (relabel μ c (canonical μ))) =
      score μ (tableauTabloid μ t)) : c=1 := by
  rw [score_tableau_column,score_tableau] at h
  have hh := full_rearrangement_eq μ _ (fun x y h => t.2 h) c⁻¹ h
  simpa using hh

end
end PartialPermutation.YoungTabloid
end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.SpechtDimension ----
namespace OAI

section
namespace PartialPermutation.YoungTabloid
noncomputable section
open Finset
open scoped Classical

lemma tableauVector_diag (μ : YoungDiagram) (t : Std μ) :
    tableauVector μ t (tableauTabloid μ t)=1 := by
  change polytabloid μ (relabel μ (tableauPerm μ t)⁻¹
    (relabel μ (tableauPerm μ t) (canonical μ)))=1
  rw [← relabel_mul,inv_mul_cancel,relabel_one,polytabloid_canonical]

lemma polytabloid_support (μ : YoungDiagram) (r : Tabloid μ) (h : polytabloid μ r≠0) :
    ∃ c : columnGroup μ, r=relabel μ c (canonical μ) := by
  apply transversal_column_orbit μ r
  by_contra hr
  exact h (alternating_zero_nontransversal μ _ (polytabloid_alternating μ) r hr)

lemma tableauVector_support (μ : YoungDiagram) (t : Std μ) (r : Tabloid μ)
    (h : tableauVector μ t r≠0) :
    ∃ c : columnGroup μ, r=relabel μ (tableauPerm μ t) (relabel μ c (canonical μ)) := by
  obtain ⟨c,hc⟩ := polytabloid_support μ _ h
  refine ⟨c,?_⟩
  have hh := congrArg (relabel μ (tableauPerm μ t)) hc
  simpa only [← relabel_mul,mul_inv_cancel,relabel_one] using hh

lemma tableauVector_triangular (μ : YoungDiagram) (s t : Std μ)
    (hne : s≠t) (h : tableauVector μ s (tableauTabloid μ t)≠0) :
    score μ (tableauTabloid μ t)<score μ (tableauTabloid μ s) := by
  obtain ⟨c,hc⟩ := tableauVector_support μ s _ h
  have hle := score_column_le μ s c
  rw [← hc] at hle
  apply lt_of_le_of_ne hle
  intro hh
  have h1 := score_column_eq μ s c (hc ▸ hh)
  subst c
  apply hne
  apply tableauTabloid_injective μ
  simpa only [Subgroup.coe_one,relabel_one,tableauTabloid] using hc.symm

lemma triangular_linearIndependent {ι α : Type*} [Fintype ι] [Fintype α]
    (v : ι → EuclideanSpace ℂ α) (r : ι → α) (k : ι → ℕ)
    (hd : ∀ i, v i (r i)=1) (ht : ∀ i j, i≠j → v i (r j)≠0 → k j<k i) :
    LinearIndependent ℂ v := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  by_contra hi
  let S := univ.filter (fun j => a j≠0)
  obtain ⟨j,hj,hmax⟩ := S.exists_max_image k ⟨i,by simpa [S] using hi⟩
  have haj : a j≠0 := (mem_filter.mp hj).2
  have hv (l : ι) (hl : l≠j) : a l * v l (r j)=0 := by
    by_cases hla : a l=0
    · simp [hla]
    have hzero : v l (r j)=0 := by
      by_contra hne
      exact (not_lt_of_ge (hmax l (by simp [S,hla]))) (ht l j hl hne)
    simp [hzero]
  have he := congrArg (fun w : EuclideanSpace ℂ α => w (r j)) ha
  have hs : (∑ l, a l * v l (r j))=a j := by
    rw [Finset.sum_eq_single j (fun l _ hl => hv l hl) (fun h => (h (mem_univ j)).elim),hd,mul_one]
  simp at he
  exact haj (hs.symm.trans he)

lemma tableauVector_independent (μ : YoungDiagram) : LinearIndependent ℂ (tableauVector μ) :=
  triangular_linearIndependent _ (tableauTabloid μ) (fun t => score μ (tableauTabloid μ t))
    (tableauVector_diag μ) (tableauVector_triangular μ)

theorem standardCount_le_specht_degree (μ : YoungDiagram) :
    Tableau.standardCount μ ≤ Module.finrank ℂ (spechtSub μ).toSubmodule := by
  let v : Std μ → (spechtSub μ).toSubmodule := fun t =>
    ⟨tableauVector μ t,(spechtSub μ).apply_mem_toSubmodule _ (polytabloid_mem_specht μ)⟩
  have hv : LinearIndependent ℂ v := LinearIndependent.of_comp
    (spechtSub μ).toSubmodule.subtype (tableauVector_independent μ)
  exact hv.fintype_card_le_finrank

end
end PartialPermutation.YoungTabloid

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.SpechtClassification ----
namespace OAI

section
namespace PartialPermutation
namespace SpechtActual
noncomputable section
open YoungTabloid DiagramCounting
open scoped Classical

lemma standardCount_le_degree {n : ℕ} (μ : Shape n) :
    Tableau.standardCount μ.1 ≤ irreducibleDegree (index μ) := by
  obtain ⟨e⟩ := index_spec μ
  have hd := e.toLinearEquiv.finrank_eq
  exact (standardCount_le_specht_degree μ.1).trans_eq hd.symm

end
end SpechtActual
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.ReciprocalBounds ----
namespace OAI

namespace PartialPermutation
noncomputable section
open scoped Classical

lemma symmetricInverseDegreeSum_le_tableaux (n : ℕ) (u : ℝ) (hu : 0 < u) :
    symmetricInverseDegreeSum n u ≤ TableauZeta.fullSum n u := by
  have he : symmetricInverseDegreeSum n u =
      ∑ μ : DiagramCounting.Shape n, (irreducibleDegree (SpechtActual.index μ):ℝ)^(-u) := by
    exact (Fintype.sum_equiv (SpechtActual.indexEquiv n) _ _ (fun _ => rfl)).symm
  rw [he]
  apply Finset.sum_le_sum
  intro μ _
  exact Real.rpow_le_rpow_of_nonpos
    (by exact_mod_cast Tableau.standardCount_pos μ.1)
    (by exact_mod_cast SpechtActual.standardCount_le_degree μ) (neg_nonpos.mpr hu.le)

theorem symmetricReciprocalDegreeBounded : SymmetricReciprocalDegreeBoundedStatement := by
  intro u hu
  obtain ⟨a,ha⟩ := TableauZeta.fullSum_bddAbove u hu
  refine ⟨a,?_⟩
  rintro x ⟨n,_,rfl⟩
  exact (symmetricInverseDegreeSum_le_tableaux n u hu).trans (ha (Set.mem_range_self n))

lemma symmetricInverseDegreeSum_le_constant {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) :
    symmetricInverseDegreeSum n u ≤ symmetricDegreeConstant u := by
  exact le_csSup (symmetricReciprocalDegreeBounded u hu) ⟨n,hn,rfl⟩

end
end PartialPermutation

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.OperatorNorm ----
namespace OAI

namespace PartialPermutation
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]

lemma norm_apply_sq_le_hsNormSq (A : Module.End ℂ V) (x : V) :
    ‖A x‖^2 ≤ hsNormSq A * ‖x‖^2 := by
  let e := stdOrthonormalBasis ℂ V
  calc
    ‖A x‖^2 = ∑ i, ‖inner ℂ (e i) (A x)‖^2 := (e.sum_sq_norm_inner_right _).symm
    _ ≤ ∑ i, ‖LinearMap.adjoint A (e i)‖^2 * ‖x‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [← LinearMap.adjoint_inner_left A]
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (inner ℂ (LinearMap.adjoint A (e i)) x))
        (norm_inner_le_norm (𝕜 := ℂ) (LinearMap.adjoint A (e i)) x) 2
    _ = hsNormSq A * ‖x‖^2 := by
      rw [← Finset.sum_mul, ← hsNormSq_eq_sum e, hsNormSq_adjoint]

lemma opNorm_sq_le_hsNormSq (A : Module.End ℂ V) :
    ‖LinearMap.toContinuousLinearMap A‖^2 ≤ hsNormSq A := by
  have h : ‖LinearMap.toContinuousLinearMap A‖ ≤ Real.sqrt (hsNormSq A) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (hsNormSq_nonneg A)]
    exact norm_apply_sq_le_hsNormSq A x
  simpa only [Real.sq_sqrt (hsNormSq_nonneg A)] using
    pow_le_pow_left₀ (norm_nonneg _) h 2

end
end PartialPermutation

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.Main ----
namespace OAI

namespace PartialPermutation
noncomputable section
open scoped Classical

theorem complementaryCosets_finite : ComplementaryCosetsFiniteStatement := by
  intro X _ _ b hb M hnonempty hdis _ V _ _ _ ρ hirr hρ f B u hf hm hu hcap
  let := hirr
  have hB : 0 ≤ B := by
    let i : Fin b := ⟨0,hb⟩
    have hp : (0:ℝ) < (blockSubgroup (M i)).index := by
      exact_mod_cast Nat.pos_of_ne_zero (blockSubgroup (M i)).index_ne_zero_of_finite
    have hz : 0 ≤ B / (blockSubgroup (M i)).index :=
      (Finset.sum_nonneg (fun (g : blockSubgroup (M i)) _ => hf (1*g))).trans (hcap i 1)
    simpa only [div_mul_cancel₀ B hp.ne'] using mul_nonneg hz hp.le
  have hsum : (∑ i, symmetricInverseDegreeSum (Fintype.card (M i)) u) ≤
      (b:ℝ)*symmetricDegreeConstant u := by
    calc
      _ ≤ ∑ _i : Fin b, symmetricDegreeConstant u := by
        apply Finset.sum_le_sum
        intro i _
        let : Nonempty (M i) := (hnonempty i).to_subtype
        exact symmetricInverseDegreeSum_le_constant (by exact Fintype.card_pos) hu
      _ = _ := by simp
  have hs : 0 ≤ ∑ i, symmetricInverseDegreeSum (Fintype.card (M i)) u := by
    exact Finset.sum_nonneg (fun _ _ => inverseDegreeSum_nonneg _ _)
  have hR : 0 ≤ (Module.finrank ℂ V : ℝ)^(-1+(u+2)/(b:ℝ)) := Real.rpow_nonneg (by positivity) _
  have hcoef : B * mass f * (Module.finrank ℂ V:ℝ)^(-1+(u+2)/(b:ℝ)) ≤
      B * (Module.finrank ℂ V:ℝ)^(-1+(u+2)/(b:ℝ)) := by
    calc
      _ ≤ B * 1 * (Module.finrank ℂ V:ℝ)^(-1+(u+2)/(b:ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hB) hR
      _ = _ := by ring
  have hHS : hsNormSq (complexFourier ρ (fun g => f g)) ≤
      b * B * symmetricDegreeConstant u * (Module.finrank ℂ V:ℝ)^(-1+(u+2)/(b:ℝ)) := by
    calc
      _ ≤ _ := by
        have h := inverse_degree_sum_transfer ρ (fun i => blockSubgroup (M i)) hb hρ
          (fun i j hij g hg k hk => blockSubgroup_commute (hdis hij) hg hk) f B u hf hu hcap
        rw [inverseDegreeSum_block_sum M u] at h
        exact h
      _ ≤ (B * (Module.finrank ℂ V:ℝ)^(-1+(u+2)/(b:ℝ))) *
          ((b:ℝ)*symmetricDegreeConstant u) :=
        mul_le_mul hcoef hsum hs (mul_nonneg hB hR)
      _ = _ := by ring
  exact ⟨hHS,(opNorm_sq_le_hsNormSq _).trans hHS⟩

end
end PartialPermutation

end OAI

-- ---- mission target ----
open OAI OAI.PartialPermutation
open scoped Classical BigOperators ComplexConjugate MonoidAlgebra
open scoped Classical

theorem solution : ComplementaryCosetsFiniteStatement := by
  first
    | exact OAI.PartialPermutation.complementaryCosets_finite
    | (apply OAI.PartialPermutation.complementaryCosets_finite <;> assumption)
    | (intros; apply OAI.PartialPermutation.complementaryCosets_finite <;> assumption)
