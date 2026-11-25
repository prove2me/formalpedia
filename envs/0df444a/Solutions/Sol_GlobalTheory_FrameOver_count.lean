-- Prove2me | solution 1 for GlobalTheory.FrameOver.count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:08:10.281519+00:00
-- url     : https://prove2.me/submissions/6b654a56-1185-4b32-9218-a71122cb4458

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSubmoduleAndHomLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeCountBoundFrames
import Theorems.Thm_GlobalTheory_FrameOver_card_coker
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_SubmoduleCount_card_submodule_and_hom_le
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameOver
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FrameOver
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V]
    [Module E V] (g : ι → V) (Φ : V →ₗ[E] (ι → E)) (a : ℕ) (u : (𝒪[F])ˣ)
    (hN : (Matrix.of fun i j => Φ (g i) j).det = algebraMap F E ((ϖ : F) ^ a * ((u : 𝒪[F]) : F)))
    (s : Set (Submodule L.O V))
    (hs : ∀ P ∈ s, (∀ i, g i ∈ P) ∧ (∀ x ∈ P, x ∈ Submodule.span E (Set.range g)) ∧
      ∀ x ∈ P, ∀ j, Φ x j ∈ L.O) :
    s.encard ≤ (resQ ϖ ^ (2 * a * Fintype.card ι) : ℕ) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨P0, hP0⟩
  · simp
  let N : Matrix ι ι L.O := fun i j => ⟨Φ (g i) j, (hs P0 hP0).2.2 _ ((hs P0 hP0).1 i) j⟩
  have hcard := card_coker L hϖ N a u (by
    rw [← hN]; exact RingHom.map_det L.O.subtype N)
  have hq : 2 ≤ resQ ϖ := (GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.2.2.2.1
  have hfin : Finite ((ι → L.O) ⧸ LinearMap.range N.vecMulLinear) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hsub := (GlobalTheory.SubmoduleCount.card_submodule_and_hom_le L
    ((ι → L.O) ⧸ LinearMap.range N.vecMulLinear) (Fintype.card ι)
    (fun i => (LinearMap.range N.vecMulLinear).mkQ (Pi.single ((Fintype.equivFin ι).symm i) 1)) (by
      have h1 : (Set.range fun i => (LinearMap.range N.vecMulLinear).mkQ
          (Pi.single ((Fintype.equivFin ι).symm i) 1)) =
          (LinearMap.range N.vecMulLinear).mkQ '' Set.range (Pi.basisFun L.O ι) := by
        rw [← Set.range_comp, ← (Fintype.equivFin ι).symm.surjective.range_comp]
        congr 1; funext i; simp
      rw [h1, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top,
        Submodule.range_mkQ])).1
  rw [hcard, ← pow_mul] at hsub
  have hunit : IsUnit (Matrix.of fun i j => Φ (g i) j).det := by
    rw [hN]
    refine (IsUnit.mk0 _ ?_).map _
    exact mul_ne_zero (pow_ne_zero _ fun h => hϖ.ne_zero (Subtype.ext h))
      fun h => u.ne_zero (Subtype.ext h)
  have hΦ : ∀ c : ι → E, Φ (∑ i, c i • g i) = Matrix.vecMul c (Matrix.of fun i j => Φ (g i) j) :=
    fun c => by
    funext j
    simp [Matrix.vecMul, dotProduct]
  have hker : ∀ x ∈ Submodule.span E (Set.range g), Φ x = 0 → x = 0 := fun x hx h0 => by
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
    rw [hΦ] at h0
    have : c = 0 := Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hunit)
      (by simpa using h0)
    simp [this]
  let Q : Submodule L.O V → Submodule L.O (ι → L.O) := fun P =>
    (P.map (Φ.restrictScalars L.O)).comap (LinearMap.compLeft (Algebra.linearMap L.O E) ι)
  have hQ : ∀ P z, z ∈ Q P ↔ ∃ x ∈ P, Φ x = fun j => (z j : E) := fun P z => Iff.rfl
  have hle : ∀ P ∈ s, LinearMap.range N.vecMulLinear ≤ Q P := by
    rintro P hP _ ⟨c, rfl⟩
    refine (hQ _ _).2 ⟨∑ i, c i • g i, P.sum_mem fun i _ => P.smul_mem _ ((hs P hP).1 i), ?_⟩
    have := hΦ fun i => c i
    refine Eq.trans this ?_
    funext j
    exact (RingHom.map_vecMul L.O.subtype N c j).symm
  have hmono : ∀ P ∈ s, ∀ P' ∈ s, Q P ≤ Q P' → P ≤ P' := fun P hP P' hP' h x hx => by
    obtain ⟨y, hy, hxy⟩ := (hQ P' fun j => ⟨Φ x j, (hs P hP).2.2 x hx j⟩).1
      (h ((hQ _ _).2 ⟨x, hx, rfl⟩))
    have := hker (x - y) (Submodule.sub_mem _ ((hs P hP).2.1 x hx) ((hs P' hP').2.1 y hy))
      (by rw [map_sub, hxy]; exact sub_self _)
    rwa [sub_eq_zero.1 this]
  have hinj : Set.InjOn (fun P => (Q P).map (LinearMap.range N.vecMulLinear).mkQ) s := by
    intro P hP P' hP' h
    have h2 := congrArg (Submodule.comap (LinearMap.range N.vecMulLinear).mkQ) h
    simp only [Submodule.comap_map_mkQ, sup_eq_right.2 (hle P hP), sup_eq_right.2 (hle P' hP')] at h2
    exact le_antisymm (hmono P hP P' hP' h2.le) (hmono P' hP' P hP h2.ge)
  rw [← hinj.encard_image]
  refine (Set.encard_le_encard (Set.subset_univ _)).trans ?_
  rw [Set.encard_univ, ENat.card_eq_coe_natCard]
  exact_mod_cast hsub
end GlobalTheory.FrameOver
