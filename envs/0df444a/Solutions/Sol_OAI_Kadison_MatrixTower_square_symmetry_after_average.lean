-- Prove2me | solution 1 for OAI.Kadison.MatrixTower.square_symmetry_after_average
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T15:27:04.960259+00:00
-- url     : https://prove2.me/submissions/ea469394-22dd-4d98-9982-f7ff72bd73c0

import Mathlib
import Definitions.Def_OAIQ039C063
import Definitions.Def_OAIQ039C067
import Definitions.Def_OAIQ039C073
import Theorems.Thm_OAI_Kadison_LittleGrothendieck_unitary_norm_le_one
import Theorems.Thm_OAI_Kadison_MatrixTower_generated_factor
import Theorems.Thm_OAI_Kadison_NormalGNS_image_bicommutant
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrix_free_symmetry_bound
import Theorems.Thm_OAI_Kadison_RepresentedTower_exists_tower_average
import Theorems.Thm_OAI_Kadison_commutator_perturbation_unitball

section
-- module Solutions.OAIQ039_CM.Commutator_NormalGNSClosure
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology ComplexOrder

open Filter

namespace Kadison.NormalGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hnormal : BoundedWOTContinuous M τ)
  (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsClosed (S : Set (H →L[ℂ] H)))
  (hSM : S≤M.toStarSubalgebra)
  (N : VonNeumannAlgebra τ.GNS)
  (hSN : ∀ a : M,(a:H →L[ℂ] H)∈S → τ.gnsStarAlgHom a∈N)

include hnormal hSM hSN in
lemma image_bicommutant_general (a : M)
    (ha : (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    τ.gnsStarAlgHom a∈N := by
  let C : Set M := {a | τ.gnsStarAlgHom a∈N}
  have hC : IsClosed C := (VonNeumannCStar.isClosed N).preimage (map_continuous τ.gnsStarAlgHom)
  have hvalC : IsClosed ((Subtype.val : M → (H →L[ℂ] H)) '' C) :=
    (VonNeumannCStar.isClosed M).isClosedMap_subtype_val C hC
  have hSC : (S : Set (H →L[ℂ] H)) ⊆ (Subtype.val : M → (H →L[ℂ] H)) '' C := by
    intro a ha
    exact ⟨⟨a,hSM ha⟩,hSN ⟨a,hSM ha⟩ ha,rfl⟩
  have hcl := closure_minimal hSC hvalC
  have hSM' : S.topologicalClosure≤M.toStarSubalgebra :=
    S.topologicalClosure_minimal hSM (VonNeumannCStar.isClosed M)
  have hSN' (b : M) (hb : (b:H →L[ℂ] H)∈S.topologicalClosure) : τ.gnsStarAlgHom b∈N := by
    have hbcl : (b:H →L[ℂ] H)∈closure (S : Set (H →L[ℂ] H)) := hb
    obtain ⟨c,hc,hcb⟩ := hcl hbcl
    have he : c=b := Subtype.ext hcb
    change τ.gnsStarAlgHom c∈N at hc
    simpa only [he] using hc
  apply image_bicommutant M τ hnormal S.topologicalClosure S.isClosed_topologicalClosure hSM' N hSN' a
  intro T hT
  apply ha T
  intro b hb
  exact hT b (S.le_topologicalClosure hb)

end Kadison.NormalGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MainCommutantDistance
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

open ContinuousLinearMap

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
lemma operator_commutator_norm_le (Y Z : K →L[ℂ] K) : ‖Y*Z-Z*Y‖≤2*‖Y‖*‖Z‖ := by
  calc
    _ ≤ ‖Y*Z‖+‖Z*Y‖ := norm_sub_le _ _
    _ ≤ ‖Y‖*‖Z‖+‖Z‖*‖Y‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalOriginalTower
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (F : ℕ → Stage M)

variable (τ : M →ₚ[ℂ] ℂ) (hnormal : NormalGNS.BoundedWOTContinuous M τ)

include hnormal in
theorem original_gns_generated (a : M) (ha : (a:H →L[ℂ] H)∈generated M F) :
    τ.gnsStarAlgHom a∈Set.centralizer (Set.centralizer
      ((⨆ n,(τ.gnsStarAlgHom.comp (F n).hom).range : StarSubalgebra ℂ (τ.GNS →L[ℂ] τ.GNS)) : Set _)) := by
  let S : StarSubalgebra ℂ (τ.GNS →L[ℂ] τ.GNS) := ⨆ n,(τ.gnsStarAlgHom.comp (F n).hom).range
  let N := NormalGNS.bicommutant S
  let T := (N.toStarSubalgebra.comap τ.gnsStarAlgHom).map M.toStarSubalgebra.subtype
  have hST : stageAlgebra M F≤T := by
    apply iSup_le
    intro n
    rintro x ⟨b,rfl⟩
    refine ⟨(F n).hom b,?_,rfl⟩
    exact NormalGNS.subset_bicommutant S
      ((le_iSup (fun n => (τ.gnsStarAlgHom.comp (F n).hom).range) n) ⟨b,rfl⟩)
  have hSN (b : M) (hb : (b:H →L[ℂ] H)∈stageAlgebra M F) : τ.gnsStarAlgHom b∈N := by
    have hbT := hST hb
    obtain ⟨c,hc,hcb⟩ := hbT
    have he : c=b := Subtype.ext hcb
    change τ.gnsStarAlgHom c∈N at hc
    simpa only [he] using hc
  exact (NormalGNS.mem_bicommutant S _).mp
    (NormalGNS.image_bicommutant_general M τ hnormal (stageAlgebra M F)
      (stageAlgebra_le M F) N hSN a ((mem_generated M F a).mp ha))

private lemma map_stage_range_le {A B : Type*}
    [Semiring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    [Semiring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
    (φ : M →⋆ₐ[ℂ] A) (ψ : A →⋆ₐ[ℂ] B) :
    (⨆ n,(φ.comp (F n).hom).range).map ψ≤
      ⨆ n,(ψ.comp (φ.comp (F n).hom)).range := by
  rw [StarSubalgebra.map_le_iff_le_comap]
  apply iSup_le
  intro n
  rintro x ⟨b,rfl⟩
  exact (le_iSup (fun n => (ψ.comp (φ.comp (F n).hom)).range) n) ⟨b,rfl⟩

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

private lemma copies_generated_of {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (φ : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (a : M)
    (ha : φ a∈Set.centralizer (Set.centralizer
      ((⨆ n,(φ.comp (F n).hom).range : StarSubalgebra ℂ (K →L[ℂ] K)) : Set _))) :
    OperatorAmplification.diagonal (H:=K) ι (φ a)∈Set.centralizer (Set.centralizer
      ((⨆ n,((OperatorAmplification.diagonal (H:=K) ι).comp (φ.comp (F n).hom)).range :
        StarSubalgebra ℂ (OperatorAmplification.SumSpace (H:=K) ι →L[ℂ]
          OperatorAmplification.SumSpace (H:=K) ι)) : Set _)) := by
  let S : StarSubalgebra ℂ (K →L[ℂ] K) := ⨆ n,(φ.comp (F n).hom).range
  let ρ := OperatorAmplification.diagonal (H:=K) ι
  have hSR := map_stage_range_le M F φ ρ
  have h := OperatorAmplification.diagonal_bicommutant ι S ha
  intro T hT
  exact h T (fun x hx => hT x (hSR hx))

include hnormal in
theorem original_copies_generated (a : M) (ha : (a:H →L[ℂ] H)∈generated M F) :
    OperatorAmplification.diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)∈
      Set.centralizer (Set.centralizer
        ((⨆ n,((OperatorAmplification.diagonal (H:=τ.GNS) ι).comp
          (τ.gnsStarAlgHom.comp (F n).hom)).range :
          StarSubalgebra ℂ (OperatorAmplification.SumSpace (H:=τ.GNS) ι →L[ℂ]
            OperatorAmplification.SumSpace (H:=τ.GNS) ι)) : Set _)) := by
  exact copies_generated_of M F ι (K:=τ.GNS) τ.gnsStarAlgHom a
    (original_gns_generated M F τ hnormal a ha)

end Kadison.MatrixTower

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalCopiesAverage
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison

namespace RepresentedTower

variable {A K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma perturbation_bound (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Y Z : K →L[ℂ] K)
    {δ : ℝ} (hδ : 0≤δ) (hd : ‖Z-Y‖≤δ)
    (hY : ∀ a : A,‖Y*ρ a-ρ a*Y‖≤δ*‖a‖) (a : A) :
    ‖Z*ρ a-ρ a*Z‖≤(3*δ)*‖a‖ := by
  have he : Z*ρ a-ρ a*Z=(Z-Y)*ρ a-ρ a*(Z-Y)+(Y*ρ a-ρ a*Y) := by
    simp only [sub_mul,mul_sub]; abel
  calc
    _ ≤ ‖(Z-Y)*ρ a-ρ a*(Z-Y)‖+‖Y*ρ a-ρ a*Y‖ := by rw [he]; exact norm_add_le _ _
    _ ≤ 2*‖Z-Y‖*‖ρ a‖+δ*‖a‖ := add_le_add (operator_commutator_norm_le _ _) (hY a)
    _ ≤ 2*δ*‖a‖+δ*‖a‖ := by
      gcongr
      exact NonUnitalStarAlgHom.norm_apply_le ρ a
    _ = _ := by ring

end RepresentedTower

namespace MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) [Nontrivial M] (F : ℕ → Stage M)

variable (τ : M →ₚ[ℂ] ℂ) (hnormal : NormalGNS.BoundedWOTContinuous M τ)

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

include hnormal in
theorem original_copies_average (hF : Monotone (fun n => (F n).hom.range))
    (Y : OperatorAmplification.SumSpace (H:=τ.GNS) ι →L[ℂ]
      OperatorAmplification.SumSpace (H:=τ.GNS) ι) {δ : ℝ} (hδ : 0≤δ)
    (hY : ∀ a : M,‖Y*OperatorAmplification.diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
      OperatorAmplification.diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Y‖≤δ*‖a‖) :
    ∃ Z : OperatorAmplification.SumSpace (H:=τ.GNS) ι →L[ℂ]
      OperatorAmplification.SumSpace (H:=τ.GNS) ι,
      ‖Z‖≤‖Y‖ ∧ ‖Z-Y‖≤δ ∧
      (∀ a : M,(a:H →L[ℂ] H)∈generated M F →
        Z*OperatorAmplification.diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)=
          OperatorAmplification.diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Z) ∧
      (∀ a : M,‖Z*OperatorAmplification.diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
        OperatorAmplification.diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Z‖≤(3*δ)*‖a‖) := by
  let ρ := (OperatorAmplification.diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom
  have hb (u : unitary M) : ‖Y*ρ (u:M)-ρ (u:M)*Y‖≤δ := by
    simpa only [ρ,StarAlgHom.comp_apply,CStarRing.norm_of_mem_unitary u.property,mul_one] using hY (u:M)
  have havg := RepresentedTower.exists_tower_average ρ (fun n => (F n).I)
    (fun n => (F n).hom) hF Y hδ hb
  obtain ⟨Z,hZ,hd,hc⟩ := havg
  refine ⟨Z,hZ,hd,?_,?_⟩
  · intro a ha
    exact hc _ (original_copies_generated M F τ hnormal ι a ha)
  · exact RepresentedTower.perturbation_bound ρ Y Z hδ hd hY

end MatrixTower

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteSquareConditionalBound
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private lemma commutator_perturbation_starHom
    {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (g : B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (Y Z : A) (s : unitary B) {b e : ℝ}
    (hb : ‖f Z*g (s:B)-g (s:B)*f Z‖ ≤ b) (he : ‖Z-Y‖ ≤ e) :
    ‖f Y*g (s:B)-g (s:B)*f Y‖ ≤ b+2*e := by
  apply commutator_perturbation_unitball (f Y) (f Z) (g (s:B)) hb
  · rw [← map_sub]
    exact (NonUnitalStarAlgHom.norm_apply_le f (Y-Z)).trans
      (by simpa only [norm_sub_rev] using he)
  · exact (NonUnitalStarAlgHom.norm_apply_le g (s:B)).trans
      (LittleGrothendieck.unitary_norm_le_one s)

namespace MatrixTower

open OperatorAmplification TracialSequence

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (i₀ : ι)

attribute [local instance] OAI.Kadison.MatrixTower.finiteSquareConditionalBoundDecidableEq
variable (M : VonNeumannAlgebra H) [Nontrivial M] (E : ℕ → Stage M)

variable (τ : M →ₚ[ℂ] ℂ) (hnormal : NormalGNS.BoundedWOTContinuous M τ)

variable (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)

variable (F : FreeCornerPosition (MatrixGNS.trace (ι:=ι) τ) ω
  (matrixVonNeumann ι i₀ (generated M E))
  (matrixInclusion ι i₀ M (generated M E) (generated_le M E)))

omit [Nonempty ι] in
include hnormal in
private theorem square_original_copies_average
    (hE : Monotone (fun n => (E n).hom.range))
    (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    {δ : ℝ} (hδ : 0≤δ)
    (hY : ∀ a : M, ‖Y*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Y‖≤δ*‖a‖) :
    ∃ Z : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι,
      ‖Z‖≤‖Y‖ ∧ ‖Z-Y‖≤δ ∧
      (∀ a : M, (a:H →L[ℂ] H)∈generated M E →
        Z*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)=
        diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Z) ∧
      (∀ a : M, ‖Z*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
        diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Z‖≤(3*δ)*‖a‖) := by
  exact original_copies_average (H:=H) M E τ hnormal ι hE Y hδ hY

include hnormal hω F in
theorem square_symmetry_after_average_oai
    (hE : Monotone (fun n => (E n).hom.range))
    (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hY : ∀ a : M,‖Y*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Y‖ ≤ δ*‖a‖)
    (s : unitary (CStarMatrix ι ι M)) (hs0 : MatrixGNS.trace (ι:=ι) τ (s:CStarMatrix ι ι M)=0)
    (hs2 : (s:CStarMatrix ι ι M)*(s:CStarMatrix ι ι M)=1) :
    ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) ι Y*MatrixGNS.representation τ (s:CStarMatrix ι ι M)-
      MatrixGNS.representation τ (s:CStarMatrix ι ι M)*diagonal (H:=SumSpace (H:=τ.GNS) ι) ι Y‖ ≤ 3122*δ := by
  have havg := square_original_copies_average ι M E τ hnormal hE Y hδ hY
  obtain ⟨Z, _, hd, hZQ, hZ⟩ := havg
  have symmetry := matrix_free_symmetry_bound (H := H) ι i₀ M
  have atGenerated := symmetry (generated M E) (generated_le M E) τ
  have atFilter := atGenerated ω hω
  change _ at *
  delta finiteSquareConditionalBoundDecidableEq matrixFreeSymmetryDecidableEq at *
  have inFreePosition := atFilter F
  have inFactor := inFreePosition (generated_factor M E hirr) hτ hfaith h1
  have forAverage := inFactor Z
  have hs := forAverage (fun q => hZQ _ q.property) (mul_nonneg (by norm_num) hδ) hZ s hs0 hs2
  have h := commutator_perturbation_starHom
    (diagonal (H:=SumSpace (H:=τ.GNS) ι) ι)
    (MatrixGNS.representation (ι:=ι) τ) Y Z s hs hd
  convert h using 1 <;> first | rfl | ring

end MatrixTower

end Kadison

end

end OAI
end

theorem solution : type_of% @OAI.Kadison.MatrixTower.square_symmetry_after_average_oai := @OAI.Kadison.MatrixTower.square_symmetry_after_average_oai
