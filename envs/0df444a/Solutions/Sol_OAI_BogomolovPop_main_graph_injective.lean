-- Prove2me | solution 1 for OAI.BogomolovPop.main_graph_injective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:47:26.5682+00:00
-- url     : https://prove2.me/submissions/ce553473-8903-4442-b952-4f109045d693

-- Generated from openai/math@1581d4c lean/OAI/Algebra/BogomolovPop/Injectivity.lean:L304-L315
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.BogomolovPop.main_graph_injective.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_BogomolovPop_main_graph_injective) verbatim and is proved by it.
import Mathlib
import Definitions.Def_BogomolovPopInjectivity
import Definitions.Def_OAI_Algebra_BogomolovPop_Foundations
import Definitions.Def_OAI_Algebra_BogomolovPop_Canonical
import Definitions.Def_OAI_Algebra_BogomolovPop_PowerCompletion
import Definitions.Def_OAI_Algebra_BogomolovPop_Kummer
import Definitions.Def_OAI_Algebra_BogomolovPop_Injectivity
import Theorems.Thm_OAI_BogomolovPop_pullback_scalar_frobenius

-- ---- from OAI.Algebra.BogomolovPop.Foundations ----
namespace OAI

/-! Literal Galois objects, quotient topology and continuous ell-adic actions. -/

noncomputable section
open scoped Topology

noncomputable section
namespace BogomolovPop

end BogomolovPop

namespace BogomolovPop
open scoped commutatorElement

end BogomolovPop

namespace BogomolovPop
open scoped commutatorElement

open Filter

variable {ell : ℕ} [Fact ell.Prime]

section Profinite
variable {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [NonarchimedeanAddGroup A] [CompactSpace A] [T2Space A]

variable [hA : Fact (AllLevelsEll ell A)]

end Profinite

theorem padic_appr_tendsto (c : PadicInt ell) :
    Tendsto (fun n : ℕ => (PadicInt.appr c n : PadicInt ell)) atTop (nhds c) := by
  have hpos : 0 < (ell : ℝ) := Nat.cast_pos.mpr (Fact.out : ell.Prime).pos
  have hlt : 1 < (ell : ℝ) := by exact_mod_cast (Fact.out : ell.Prime).one_lt
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
  · intro n
    have hb := (PadicInt.norm_le_pow_iff_mem_span_pow (c - (PadicInt.appr c n : PadicInt ell)) n).mpr
      (PadicInt.appr_spec n c)
    simpa only [dist_eq_norm, norm_sub_rev, zpow_neg, zpow_natCast, inv_pow] using hb
  · simpa only [inv_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hpos.le) (inv_lt_one_of_one_lt₀ hlt)

theorem padic_appr_smul_tendsto {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [Module (PadicInt ell) A] [ContinuousSMul (PadicInt ell) A]
    (c : PadicInt ell) (x : A) :
    Tendsto (fun n : ℕ => PadicInt.appr c n • x) atTop (nhds (c • x)) := by
  simpa only [Nat.cast_smul_eq_nsmul] using (padic_appr_tendsto c).smul_const x

end BogomolovPop

end
end

end OAI

-- ---- from OAI.Algebra.BogomolovPop.Canonical ----
namespace OAI

/-! Canonical Galois transport, bracket compatibility and quotient-map well-definedness. -/

noncomputable section
open scoped Topology

namespace BogomolovPop
open scoped Topology commutatorElement
open Filter

theorem scalarStep_iff_unit {ell : ℕ} [Fact ell.Prime] {K L : Type*} [Field K] [Field L]
    (φ χ : IsomC ell K L) :
    ScalarStep φ χ ↔ ∃ u : (PadicInt ell)ˣ, ∀ x : PiA ell L,
      Additive.ofMul (χ.1 x) = (u : PadicInt ell) • Additive.ofMul (φ.1 x) := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, fun x => ?_⟩
    exact tendsto_nhds_unique (hu x) (padic_appr_smul_tendsto (u : PadicInt ell) (Additive.ofMul (φ.1 x)))
  · rintro ⟨u, hu⟩
    refine ⟨u, fun x => ?_⟩
    have ht := padic_appr_smul_tendsto (u : PadicInt ell) (Additive.ofMul (φ.1 x))
    rw [← hu x] at ht
    exact ht

theorem scalarStep_equivalence {ell : ℕ} [Fact ell.Prime] {K L : Type*} [Field K] [Field L] :
    Equivalence (ScalarStep (ell := ell) (K := K) (L := L)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro φ
    rw [scalarStep_iff_unit]
    exact ⟨1, fun x => by simp⟩
  · intro φ χ h
    obtain ⟨u, hu⟩ := (scalarStep_iff_unit φ χ).mp h
    rw [scalarStep_iff_unit]
    exact ⟨u⁻¹, fun x => by rw [hu, ← mul_smul]; simp⟩
  · intro φ χ ψ h h'
    obtain ⟨u, hu⟩ := (scalarStep_iff_unit φ χ).mp h
    obtain ⟨v, hv⟩ := (scalarStep_iff_unit χ ψ).mp h'
    rw [scalarStep_iff_unit]
    exact ⟨v * u, fun x => by rw [hv, hu, Units.val_mul, mul_smul]⟩

theorem scalarEqvGen_iff {ell : ℕ} [Fact ell.Prime] {K L : Type*} [Field K] [Field L]
    (φ χ : IsomC ell K L) :
    Relation.EqvGen ScalarStep φ χ ↔ ScalarStep φ χ := by
  exact scalarStep_equivalence.eqvGen_iff

end BogomolovPop

namespace BogomolovPop
open scoped Topology commutatorElement

end BogomolovPop

noncomputable section
namespace BogomolovPop
open scoped Topology

end BogomolovPop

namespace BogomolovPop
open scoped Topology

theorem pullbackGraph_of_extension (ell : ℕ) {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    (α : PerfectIsom k K l L) (β : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α.1 x : AlgebraicClosure L)) :
    PullbackGraph α (isomCOfExtension ell α.1 β hβ) := by
  refine ⟨β, hβ, ?_⟩
  intro σ
  refine ⟨absoluteConjugate α.1 β hβ σ, ?_, rfl⟩
  intro x
  exact β.apply_symm_apply _

end BogomolovPop

namespace BogomolovPop

theorem pullbackGraph_eq_extension (ell : ℕ) {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    (α : PerfectIsom k K l L) (φ : IsomC ell K L) (hφ : PullbackGraph α φ) :
    φ = isomCOfExtension ell α.1 (extendPerfectEquiv α.1) (extendPerfectEquiv_spec α.1) := by
  obtain ⟨β, hβ, h⟩ := hφ
  have heq : φ = isomCOfExtension ell α.1 β hβ := by
    apply Subtype.ext
    ext x
    obtain ⟨σ, rfl⟩ := absoluteToPiA_surjective ell L x
    obtain ⟨τ, hτ, hφτ⟩ := h σ
    have hτ' : τ = absoluteConjugate α.1 β hβ σ := by
      apply AlgEquiv.ext
      intro x
      apply β.injective
      exact (hτ x).trans (β.apply_symm_apply _).symm
    change φ.1 (absoluteToPiA ell L σ) =
      absoluteToPiA ell K (absoluteConjugate α.1 β hβ σ)
    exact hφτ.trans (congrArg (absoluteToPiA ell K) hτ')
  exact heq.trans (isomCOfExtension_eq ell α.1 β (extendPerfectEquiv α.1) hβ
    (extendPerfectEquiv_spec α.1))

end BogomolovPop

namespace BogomolovPop

theorem canonicalPullback_spec (ell : ℕ) {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    (α : PerfectIsom k K l L) : PullbackGraph α (canonicalPullback ell α) :=
  pullbackGraph_of_extension ell α _ (extendPerfectEquiv_spec α.1)

theorem phiGraph_eq_canonicalPhi (ell : ℕ) [Fact ell.Prime] {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    {a : IsomF k K l L} {b : IsomCUnits ell K L} (h : PhiGraph a b) :
    b = canonicalPhi ell a := by
  obtain ⟨α, φ, rfl, rfl, hφ⟩ := h
  change Quotient.mk _ φ = Quotient.mk _ (canonicalPullback ell α)
  rw [pullbackGraph_eq_extension ell α φ hφ]
  rfl

end BogomolovPop

namespace BogomolovPop

end BogomolovPop

end
end

end OAI

-- ---- from OAI.Algebra.BogomolovPop.Injectivity ----
namespace OAI

/-! Perfect-closure descent and injectivity of the canonical orbit map. -/

noncomputable section
open scoped Topology

noncomputable section
namespace BogomolovPop

end BogomolovPop

namespace BogomolovPop
end BogomolovPop
namespace BogomolovPop
open scoped Topology
end BogomolovPop

namespace BogomolovPop
open scoped Topology

theorem main_canonical_injective (ell : ℕ) [Fact ell.Prime]
    (k K l L : Type*) [Field k] [Field K] [Field l] [Field L]
    [IsAlgClosed k] [IsAlgClosed l] [Algebra k K] [Algebra l L]
    [Algebra.EssFiniteType k K] [Algebra.EssFiniteType l L]
    (hk : (ell : k) ≠ 0) (_hl : (ell : l) ≠ 0)
    (hK : 2 ≤ Algebra.trdeg k K) (_hL : 2 ≤ Algebra.trdeg l L) :
    Function.Injective (canonicalPhi ell (k := k) (K := K) (l := l) (L := L)) := by
  have hchar : (ell : K) ≠ 0 := by
    simpa only [map_natCast] using (map_ne_zero (algebraMap k K)).mpr hk
  have ht : Algebra.Transcendental k K := trdeg_ne_zero_iff.mp (by
    intro he
    rw [he] at hK
    norm_num at hK)
  let := ht
  have hx : ∃ x : K, Transcendental k x := Algebra.Transcendental.transcendental
  intro a b hab
  induction a using Quotient.inductionOn with | h α =>
    induction b using Quotient.inductionOn with | h β =>
      apply Quotient.sound
      change Quotient.mk _ (canonicalPullback ell α) = Quotient.mk _ (canonicalPullback ell β) at hab
      have hs := (scalarEqvGen_iff (canonicalPullback ell α) (canonicalPullback ell β)).mp
        (Quotient.exact hab)
      exact pullback_scalar_frobenius ell hchar hx α β _ _
        (canonicalPullback_spec ell α) (canonicalPullback_spec ell β) hs
end BogomolovPop

namespace BogomolovPop

/-- Injectivity of the canonical Galois graph on its prescribed orbit sets. -/
theorem main_graph_injective (ell : ℕ) [Fact ell.Prime]
    (k K l L : Type*) [Field k] [Field K] [Field l] [Field L]
    [IsAlgClosed k] [IsAlgClosed l] [Algebra k K] [Algebra l L]
    [Algebra.EssFiniteType k K] [Algebra.EssFiniteType l L]
    (hk : (ell : k) ≠ 0) (hl : (ell : l) ≠ 0)
    (hK : 2 ≤ Algebra.trdeg k K) (hL : 2 ≤ Algebra.trdeg l L) :
    ∀ (a a' : IsomF k K l L) (b : IsomCUnits ell K L),
      PhiGraph a b → PhiGraph a' b → a = a'  := by
  intro a a' b ha ha'
  apply main_canonical_injective ell k K l L hk hl hK hL
  exact (phiGraph_eq_canonicalPhi ell ha).symm.trans (phiGraph_eq_canonicalPhi ell ha')

end BogomolovPop

end
end

end OAI

-- ---- mission target ----
open OAI OAI.BogomolovPop
open scoped Topology

theorem solution (ell : ℕ) [Fact ell.Prime]
    (k K l L : Type*) [Field k] [Field K] [Field l] [Field L]
    [IsAlgClosed k] [IsAlgClosed l] [Algebra k K] [Algebra l L]
    [Algebra.EssFiniteType k K] [Algebra.EssFiniteType l L]
    (hk : (ell : k) ≠ 0) (hl : (ell : l) ≠ 0)
    (hK : 2 ≤ Algebra.trdeg k K) (hL : 2 ≤ Algebra.trdeg l L) :
    ∀ (a a' : IsomF k K l L) (b : IsomCUnits ell K L),
      PhiGraph a b → PhiGraph a' b → a = a' := by
  first
    | exact OAI.BogomolovPop.main_graph_injective ell k K l L hk hl hK hL
    | exact OAI.BogomolovPop.main_graph_injective
    | (apply OAI.BogomolovPop.main_graph_injective <;> assumption)
    | (intros; apply OAI.BogomolovPop.main_graph_injective <;> assumption)
