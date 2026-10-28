-- Prove2me | solution 1 for OAI.Heisenberg.cubeBoundary_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T08:34:51.916179+00:00
-- url     : https://prove2.me/submissions/8c047e45-ce22-4f5a-9ced-d537f022823b

import Mathlib
import Definitions.Def_Heisenberg
import Definitions.Def_OAIW2HM002
import Theorems.Thm_OAI_Heisenberg_dynamics_converges

section
-- module Solutions.OAIW2_Heis.Heisenberg_LocalAlgebra
attribute [-instance] _root_.OAI.Heisenberg.quasiLocalClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical

open scoped ComplexConjugate BigOperators
namespace Heisenberg

lemma localUnit_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d}
    (hx : x ∈ F) (a b : Level ℓ) : localUnit d ℓ x a b ∈ localAlgebra d ℓ F :=
  StarAlgebra.subset_adjoin ℂ _ ⟨x, hx, a, b, rfl⟩

lemma spinZ_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinZ d ℓ x ∈ localAlgebra d ℓ F := by
  apply Subalgebra.sum_mem
  intro k _
  exact (localAlgebra d ℓ F).smul_mem (localUnit_mem_localAlgebra d ℓ F hx k k) _

lemma spinPlus_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinPlus d ℓ x ∈ localAlgebra d ℓ F := by
  apply Subalgebra.sum_mem
  intro k _
  exact (localAlgebra d ℓ F).smul_mem (localUnit_mem_localAlgebra d ℓ F hx k.succ k.castSucc) _

lemma spinMinus_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinMinus d ℓ x ∈ localAlgebra d ℓ F :=
  star_mem (spinPlus_mem_localAlgebra d ℓ F hx)

lemma spinX_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinX d ℓ x ∈ localAlgebra d ℓ F :=
  (localAlgebra d ℓ F).smul_mem ((localAlgebra d ℓ F).add_mem
    (spinPlus_mem_localAlgebra d ℓ F hx) (spinMinus_mem_localAlgebra d ℓ F hx)) _

lemma spinY_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinY d ℓ x ∈ localAlgebra d ℓ F :=
  (localAlgebra d ℓ F).smul_mem ((localAlgebra d ℓ F).sub_mem
    (spinPlus_mem_localAlgebra d ℓ F hx) (spinMinus_mem_localAlgebra d ℓ F hx)) _

theorem localAlgebras_commute {d ℓ : ℕ} {F G : Set (Site d)} (hFG : Disjoint F G)
    {A B : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ F) (hB : B ∈ localAlgebra d ℓ G) :
    Commute A B := by
  have hg (x : Site d) (hx : x ∈ F) (a b : Level ℓ) :
      localAlgebra d ℓ G ≤ StarSubalgebra.centralizer ℂ {localUnit d ℓ x a b} := by
    apply StarAlgebra.adjoin_le
    rintro _ ⟨y, hy, c, e, rfl⟩
    have hxy : x ≠ y := fun h => (Set.disjoint_left.mp hFG hx) (h ▸ hy)
    change _ ∈ StarSubalgebra.centralizer ℂ _
    rw [StarSubalgebra.mem_centralizer_iff ℂ]
    rintro _ rfl
    exact ⟨(localUnits_commute hxy a b c e).eq, by
      rw [star_localUnit]
      exact (localUnits_commute hxy b a c e).eq⟩
  have hle : localAlgebra d ℓ F ≤ StarSubalgebra.centralizer ℂ {B} := by
    apply StarAlgebra.adjoin_le
    rintro _ ⟨x, hx, a, b, rfl⟩
    have h₁ := ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hg x hx a b hB)) _ (Set.mem_singleton _)
    have h₂ := ((StarSubalgebra.mem_centralizer_iff ℂ).mp
      (hg x hx a b (star_mem hB))) _ (Set.mem_singleton _)
    change _ ∈ StarSubalgebra.centralizer ℂ _
    rw [StarSubalgebra.mem_centralizer_iff ℂ]
    rintro _ rfl
    exact ⟨h₁.1.symm, h₂.1.symm⟩
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle hA)) B (Set.mem_singleton B)).1.symm

lemma singleton_local_commute {d ℓ : ℕ} {x y : Site d} (hxy : x ≠ y)
    {A B : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ {x})
    (hB : B ∈ localAlgebra d ℓ {y}) : Commute A B :=
  localAlgebras_commute (Set.disjoint_singleton.mpr hxy) hA hB

lemma nearestNeighbor_ne {d : ℕ} {x y : Site d} (h : NearestNeighbor x y) : x ≠ y := by
  intro he
  subst y
  simp [NearestNeighbor] at h

theorem star_hamiltonian (d ℓ : ℕ) (Λ : Finset (Site d)) :
    star (hamiltonian d ℓ Λ) = hamiltonian d ℓ Λ := by
  classical
  simp only [hamiltonian, star_neg, star_sum, star_add, star_mul,
    star_spinX, star_spinY, star_spinZ]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  have hxy := nearestNeighbor_ne (Finset.mem_filter.mp he).2.1
  have hX := singleton_local_commute hxy (spinX_mem_localAlgebra d ℓ {e.1} rfl)
    (spinX_mem_localAlgebra d ℓ {e.2} rfl)
  have hY := singleton_local_commute hxy (spinY_mem_localAlgebra d ℓ {e.1} rfl)
    (spinY_mem_localAlgebra d ℓ {e.2} rfl)
  have hZ := singleton_local_commute hxy (spinZ_mem_localAlgebra d ℓ {e.1} rfl)
    (spinZ_mem_localAlgebra d ℓ {e.2} rfl)
  rw [hX.eq, hY.eq, hZ.eq]

lemma imaginaryTime_skew (t : ℝ) : Complex.I * (t : ℂ) ∈ skewAdjoint ℂ := by
  change star (Complex.I * (t : ℂ)) = -(Complex.I * (t : ℂ))
  simp

lemma hamiltonian_selfAdjoint (d ℓ : ℕ) (Λ : Finset (Site d)) :
    IsSelfAdjoint (hamiltonian d ℓ Λ) := star_hamiltonian d ℓ Λ

lemma timeHamiltonian_skew (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    (Complex.I * (t : ℂ)) • hamiltonian d ℓ Λ ∈ skewAdjoint (QuasiLocal d ℓ) :=
  IsSelfAdjoint.smul_mem_skewAdjoint (imaginaryTime_skew t) (hamiltonian_selfAdjoint d ℓ Λ)

lemma finiteUnitary (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • hamiltonian d ℓ Λ) ∈ unitary (QuasiLocal d ℓ) :=
  NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (timeHamiltonian_skew d ℓ Λ t)

lemma finiteInverseUnitary (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    NormedSpace.exp ((-(Complex.I * (t : ℂ))) • hamiltonian d ℓ Λ) ∈ unitary (QuasiLocal d ℓ) := by
  convert finiteUnitary d ℓ Λ (-t) using 1; simp

theorem norm_finiteDynamics (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) (A : QuasiLocal d ℓ) :
    ‖finiteDynamics d ℓ Λ t A‖ = ‖A‖ := by
  rw [finiteDynamics, CStarRing.norm_mul_mem_unitary _ (finiteInverseUnitary d ℓ Λ t),
    CStarRing.norm_mem_unitary_mul _ (finiteUnitary d ℓ Λ t)]

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_StateCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators
open Filter Topology Metric
open scoped NNReal
open scoped NNReal

namespace Heisenberg

open scoped ComplexOrder

theorem positive_norm_bound {E : Type*} [CStarAlgebra E] [PartialOrder E]
    [StarOrderedRing E] (φ : E →L[ℂ] ℂ) (hn : φ 1 = 1)
    (hpos : ∀ B, 0 ≤ φ (star B * B)) : ‖φ‖ ≤ 4 := by
  have hp : ∀ A : E, 0 ≤ A → 0 ≤ φ A := by
    intro A hA
    obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
    exact hpos B
  let f : E →ₚ[ℂ] ℂ :=
    { φ.toLinearMap with
      monotone' := by
        intro A B h
        change φ A ≤ φ B
        have h' := hp (B - A) (sub_nonneg.mpr h)
        simpa only [map_sub, sub_nonneg] using h' }
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro A
  obtain ⟨x, hx, hnorm, hA⟩ := CStarAlgebra.exists_sum_four_nonneg A
  conv_lhs => rw [hA, map_sum]
  calc
    ‖∑ i : Fin 4, φ (Complex.I ^ (i : ℕ) • x i)‖ ≤
        ∑ i : Fin 4, ‖φ (Complex.I ^ (i : ℕ) • x i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul, norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
      have hi := PositiveLinearMap.norm_apply_le_of_nonneg f (x i) (hx i)
      change ‖φ (x i)‖ ≤ ‖φ 1‖ * ‖x i‖ at hi
      simpa only [hn, norm_one, one_mul] using hi.trans
        (by simpa only [hn, norm_one, one_mul] using hnorm i)
    _ = 4 * ‖A‖ := by simp

theorem state_norm_bound {d ℓ : ℕ} (ω : State d ℓ) : ‖ω.functional‖ ≤ 4 := by
  let : PartialOrder (QuasiLocal d ℓ) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (QuasiLocal d ℓ) := CStarAlgebra.spectralOrderedRing _
  exact positive_norm_bound ω.functional ω.normalized
    (fun B => ⟨(ω.positive B).2, by simpa using (ω.positive B).1.symm⟩)

open scoped InnerProductSpace

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_BoundedStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators
open Filter Topology Metric
open scoped NNReal
open scoped NNReal

open scoped ComplexConjugate Topology
namespace GibbsStrip
variable {E : Type*} [CStarAlgebra E]

attribute [local instance] OAI.GibbsStrip.instNormedAlgebraRat_solutions
lemma real_evolve_norm {K : E} (hK : IsSelfAdjoint K) (t : ℝ) (A : E) :
    ‖evolve K (t : ℂ) A‖ = ‖A‖ := by
  have h (t : ℝ) : NormedSpace.exp ((Complex.I*(t:ℂ)) • K) ∈ unitary E := by
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    apply IsSelfAdjoint.smul_mem_skewAdjoint _ hK
    change star (Complex.I*(t:ℂ)) = -(Complex.I*(t:ℂ))
    simp
  have hn : NormedSpace.exp ((-(Complex.I*(t:ℂ))) • K) ∈ unitary E := by
    convert h (-t) using 1; simp
  rw [evolve,CStarRing.norm_mul_mem_unitary _ hn,CStarRing.norm_mem_unitary_mul _ (h t)]

end GibbsStrip

open Set Filter Complex
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_GibbsLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators
open Filter Topology Metric
open scoped NNReal
open scoped ComplexConjugate Topology
open Set Filter Complex
open scoped Topology

namespace Heisenberg

open GibbsStrip

lemma state_apply_norm_le {d ℓ : ℕ} (ω : State d ℓ) (A : QuasiLocal d ℓ) :
    ‖ω.functional A‖ ≤ 4 * ‖A‖ :=
  (ω.functional.le_opNorm A).trans (mul_le_mul_of_nonneg_right (state_norm_bound ω) (norm_nonneg A))

open Filter Topology GibbsStrip

end Heisenberg
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg
open SlotTensor TensorMatrix
variable {d ℓ : ℕ}

lemma totalZ_selfAdjoint (Λ : Finset (Site d)) : IsSelfAdjoint (totalZ (ℓ:=ℓ) Λ) := by
  change star (totalZ Λ)=totalZ Λ
  simp only [totalZ,star_sum,star_spinZ]

lemma shiftedField_selfAdjoint (Λ : Finset (Site d)) (h : ℝ) :
    IsSelfAdjoint (shiftedField (ℓ:=ℓ) Λ h) := by
  change star (shiftedField Λ h)=shiftedField Λ h
  simp only [shiftedField,star_sub,star_add,star_smul,star_trivial,star_one,
    (hamiltonian_selfAdjoint d ℓ Λ).star_eq,(totalZ_selfAdjoint (ℓ:=ℓ) Λ).star_eq]

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CubeSurface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators
open Filter Topology
namespace Heisenberg
open SpatialFrame
variable {d ℓ : ℕ}

lemma box_mono {n m : ℕ} (hnm : n≤ m) : box d n⊆box d m := by
  intro x hx
  apply (box_mem d m x).mpr
  intro j
  exact (box_mem d n x |>.mp hx j).trans (by exact_mod_cast hnm)

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg

variable {d ℓ : ℕ}

lemma averageState_apply {I : Type*} [Fintype I] (μ : I → ℝ) (hμ : ∀ i,0≤μ i)
    (hm : ∑ i,μ i=1) (ω : I → State d ℓ) (A : QuasiLocal d ℓ) :
    (averageState μ hμ hm ω).functional A=∑ i,(μ i:ℂ)*(ω i).functional A := by
  simp only [averageState,sum_apply,smul_apply,smul_eq_mul]

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinBulk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg
variable {d ℓ : ℕ}

lemma box_add_mem {N r : ℕ} {x y : Site d} (hx : x∈box d N) (hy : y∈box d r) : x+y∈box d (N+r) := by
  apply (box_mem _ _ _).mpr
  intro i
  exact (abs_add_le (x i) (y i)).trans (by
    simpa only [Nat.cast_add] using add_le_add ((box_mem _ _ _).mp hx i) ((box_mem _ _ _).mp hy i))

lemma box_deep_translate {N r : ℕ} (hr : r≤N) {x : Site d} (hx : x∈box d (N-r)) :
    box d r⊆(box d N).image (fun y=>-x+y) := by
  intro y hy
  refine Finset.mem_image.mpr ⟨x+y,?_,by simp only [←add_assoc,neg_add_cancel,zero_add]⟩
  simpa only [Nat.sub_add_cancel hr] using box_add_mem hx hy

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_FiniteAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Average
variable {X E : Type*} [DecidableEq X] [NormedAddCommGroup E]

lemma norm_sum_bulk_le (Λ F : Finset X) (hF : F⊆Λ) (f : X → E) (δ C : ℝ)
    (hgood : ∀ x∈F,‖f x‖≤δ) (hall : ∀ x∈Λ,‖f x‖≤C) :
    ‖∑ x∈Λ,f x‖≤(F.card:ℝ)*δ+((Λ\F).card:ℝ)*C := by
  rw [←Finset.sum_sdiff hF]
  calc _ ≤ ‖∑ x∈Λ\F,f x‖+‖∑ x∈F,f x‖ := norm_add_le _ _
       _ ≤ (∑ _∈Λ\F,C)+(∑ _∈F,δ) := add_le_add
         ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun x hx=>hall x (Finset.mem_sdiff.mp hx).1)))
         ((norm_sum_le _ _).trans (Finset.sum_le_sum hgood))
       _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

lemma norm_uniform_bulk_le (Λ F : Finset X) (hΛ : Λ.Nonempty) (hF : F⊆Λ)
    (f : X → ℂ) {δ C : ℝ} (hδ : 0≤δ)
    (hgood : ∀ x∈F,‖f x‖≤δ) (hall : ∀ x∈Λ,‖f x‖≤C) :
    ‖(Λ.card:ℂ)⁻¹*∑ x∈Λ,f x‖≤δ+(((Λ\F).card:ℝ)/(Λ.card:ℝ))*C := by
  have hp : (0:ℝ)<Λ.card := by exact_mod_cast Finset.card_pos.mpr hΛ
  rw [norm_mul,norm_inv,Complex.norm_natCast]
  calc _ ≤ (Λ.card:ℝ)⁻¹*((F.card:ℝ)*δ+((Λ\F).card:ℝ)*C) :=
         mul_le_mul_of_nonneg_left (norm_sum_bulk_le Λ F hF f δ C hgood hall) (inv_nonneg.mpr hp.le)
       _ ≤ (Λ.card:ℝ)⁻¹*((Λ.card:ℝ)*δ+((Λ\F).card:ℝ)*C) := by
         gcongr
       _ = _ := by field_simp

end Heisenberg.Average
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinCubeAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg
variable {d ℓ : ℕ}

lemma cubeAverage_apply (Λ : Finset (Site d)) (hΛ : Λ.Nonempty) (ω : State d ℓ) (A : QuasiLocal d ℓ) :
    (cubeAverage Λ hΛ ω).functional A=(Λ.card:ℂ)⁻¹*∑ x∈Λ,ω.functional (translation d ℓ x A) := by
  classical
  simp only [cubeAverage,averageState_apply,translatedState,ContinuousLinearMap.comp_apply,translationLinear_apply]
  rw [←Finset.mul_sum]
  have hs : (∑ i : Λ,ω.functional (translation d ℓ i.val A))=∑ x∈Λ,ω.functional (translation d ℓ x A) := Finset.sum_coe_sort Λ (fun x=>ω.functional (translation d ℓ x A))
  rw [hs]
  simp only [Complex.ofReal_inv,Complex.ofReal_natCast]

end Heisenberg
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpinAverageBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg
variable {d ℓ : ℕ}

lemma dynamics_norm (t : ℝ) (B : QuasiLocal d ℓ) : ‖dynamics d ℓ t B‖=‖B‖ := by
  classical
  have h:=((dynamics_converges d ℓ t B).norm)
  have hn (n : ℕ) := norm_finiteDynamics d ℓ (box d n) t B
  simp only [hn] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

lemma translated_state_difference (ω : State d ℓ) (x : Site d)
    (M : QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ) (v w : QuasiLocal d ℓ) :
    ‖ω.functional (translation d ℓ x (M v))-ω.functional (translation d ℓ x (M w))‖≤4*‖M‖*dist v w := by
  rw [←map_sub ω.functional _ _,←map_sub (translation d ℓ x) _ _,←map_sub M _ _,dist_eq_norm]
  calc _ ≤ 4*‖translation d ℓ x (M (v-w))‖ := state_apply_norm_le ω _
       _ ≤ 4*(‖M‖*‖v-w‖) := by rw [norm_translation]; exact mul_le_mul_of_nonneg_left (M.le_opNorm _) (by norm_num)
       _ = _ := by ring

lemma cubeBoundary_error_oai (N r : ℕ) (hr : r≤N) (ω : State d ℓ) (h t : ℝ)
    (M : QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ) (B : QuasiLocal d ℓ)
    {δ : ℝ} (hδ : 0≤δ)
    (hgood : ∀ Γ : Finset (Site d),box d r⊆Γ →
      dist (GibbsStrip.evolve (shiftedField Γ h) t B) (dynamics d ℓ t B)≤δ) :
    ‖cubeBoundary (box d N) ω h M B t-
      (cubeAverage (box d N) (box_nonempty d N) ω).functional (M (dynamics d ℓ t B))‖≤
        4*‖M‖*δ+(((box d N\box d (N-r)).card:ℝ)/(box d N).card)*(8*‖M‖*‖B‖) := by
  classical
  rw [cubeBoundary,cubeAverage_apply,←mul_sub,←Finset.sum_sub_distrib]
  apply Average.norm_uniform_bulk_le _ (box d (N-r)) (box_nonempty d N) (box_mono (Nat.sub_le N r)) _ (by positivity)
  · intro x hx
    exact (translated_state_difference ω _ M _ _).trans (mul_le_mul_of_nonneg_left (hgood _ (box_deep_translate hr hx)) (by positivity))
  · intro x _
    have hb : dist (GibbsStrip.evolve (shiftedField ((box d N).image (fun y=>-x+y)) h) t B) (dynamics d ℓ t B)≤2*‖B‖ := by
      classical
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans_eq (by rw [GibbsStrip.real_evolve_norm (shiftedField_selfAdjoint _ _),dynamics_norm]; ring)
    exact (translated_state_difference ω _ M _ _).trans (by nlinarith [mul_le_mul_of_nonneg_left hb (show 0≤4*‖M‖ by positivity)])

end Heisenberg
end
end

end OAI
end

theorem solution : type_of% @OAI.Heisenberg.cubeBoundary_error_oai := @OAI.Heisenberg.cubeBoundary_error_oai
