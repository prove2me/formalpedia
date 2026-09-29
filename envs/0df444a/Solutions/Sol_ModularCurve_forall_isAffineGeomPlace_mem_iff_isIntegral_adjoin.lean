-- Prove2me | solution 1 for ModularCurve.forall_isAffineGeomPlace_mem_iff_isIntegral_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/d297901f-da11-5e93-af06-d4a142a2ebd7

import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_forall_isAffineGeomPlace_mem_iff_isIntegral_adjoin
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace AffinePlaceIntegrality

private theorem mem_of_isIntegral_of_le {F : Type*} [Field F] (S : Subring F) (V : ValuationSubring F)
    (hSV : S ≤ V.toSubring) {x : F} (hx : IsIntegral ↥S x) : x ∈ V := by
  obtain ⟨p, hmon, hp⟩ := hx
  have hxV : IsIntegral ↥V x := by
    refine ⟨p.map (Subring.inclusion hSV), hmon.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hp
  obtain ⟨y, hy⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := ↥V) (A := F)).mp hxV
  rw [← hy]
  exact y.2

private theorem forall_mem_of_isIntegral {N : ℕ} [NeZero N] {k : Type*} [Field k] (f : ↥(modularFunctionFieldC k N))
    (hf : IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N))) f)
    (u : Place k (modularFunctionFieldC k N)) (hu : IsAffineGeomPlace k N u) : f ∈ u.toValuationSubring := by
  have hle : (Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N))).toSubring
      ≤ u.toValuationSubring.toSubring := by
    intro y hy
    rw [Subalgebra.mem_toSubring] at hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact hu.1
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hu.2
    | algebraMap r => exact u.algebraMap_mem' r
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  exact mem_of_isIntegral_of_le _ _ hle hf

private theorem isPrincipalIdealRing_of_ne_top {N : ℕ} [NeZero N] {k : Type*} [Field k] (hN : (N : k) ≠ 0)
    (V : ValuationSubring ↥(modularFunctionFieldC k N))
    (hk : ∀ a : k, algebraMap k ↥(modularFunctionFieldC k N) a ∈ V) (hV : V ≠ ⊤) : IsPrincipalIdealRing ↥V := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  have hsep := isSeparable_jqNModC_of_natCast_ne_zero k N hN
  haveI := (finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC k N data hsep).1
  exact ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin
    ((⟨jqModC k, jqModC_mem k N⟩ : ↥(modularFunctionFieldC k N))) V hk hV

private theorem isIntegral_of_forall_mem {N : ℕ} [NeZero N] {k : Type*} [Field k] (hN : (N : k) ≠ 0)
    (f : ↥(modularFunctionFieldC k N))
    (hf : ∀ u : Place k (modularFunctionFieldC k N), IsAffineGeomPlace k N u → f ∈ u.toValuationSubring) :
    IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N))) f := by
  set s : Set ↥(modularFunctionFieldC k N) :=
    Set.range (algebraMap k ↥(modularFunctionFieldC k N)) ∪ {jGeomGen k N, jNGeomGen k N} with hs

  have hmem : f ∈ (⨅ V : {V : ValuationSubring ↥(modularFunctionFieldC k N) // s ⊆ V.toSubring},
      V.1.toSubring) := by
    rw [Subring.mem_iInf]
    rintro ⟨V, hsV⟩
    by_cases hVtop : V = ⊤
    · change f ∈ V
      rw [hVtop]
      exact ValuationSubring.mem_top f
    · have hk : ∀ a : k, algebraMap k ↥(modularFunctionFieldC k N) a ∈ V := fun a => hsV (Or.inl ⟨a, rfl⟩)
      let u : Place k (modularFunctionFieldC k N) :=
        ⟨V, hk, hVtop, isPrincipalIdealRing_of_ne_top hN V hk hVtop⟩
      have hJ : jGeomGen k N ∈ V := hsV (Or.inr (Or.inl rfl))
      have hJN : jNGeomGen k N ∈ V := hsV (Or.inr (Or.inr rfl))
      exact hf u ⟨hJ, hJN⟩
  rw [iInf_valuationSubring_superset] at hmem
  have hint : IsIntegral ↥(Subring.closure s) f := by
    have := hmem
    rw [Subalgebra.mem_toSubring, mem_integralClosure_iff] at this
    exact this

  have hle : Subring.closure s
      ≤ (Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N))).toSubring := by
    rw [Subring.closure_le]
    rintro y (⟨a, rfl⟩ | hy)
    · exact Subalgebra.algebraMap_mem _ a
    · exact Algebra.subset_adjoin hy
  let φ : ↥(Subring.closure s) →+*
      ↥(Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N))) :=
    { toFun := fun y => ⟨y.1, hle y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  obtain ⟨p, hmon, hp⟩ := hint
  refine ⟨p.map φ, hmon.map φ, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hp

end AffinePlaceIntegrality

theorem solution
    {N : ℕ} [NeZero N] {k : Type*} [Field k] (hN : (N : k) ≠ 0) (f : ↥(modularFunctionFieldC k N)) :
    (∀ u : Place k (modularFunctionFieldC k N), IsAffineGeomPlace k N u → f ∈ u.toValuationSubring) ↔
      IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N))) f := by
  exact ⟨AffinePlaceIntegrality.isIntegral_of_forall_mem hN f, fun hf u hu => AffinePlaceIntegrality.forall_mem_of_isIntegral f hf u hu⟩

end

end S_ModularCurve_forall_isAffineGeomPlace_mem_iff_isIntegral_adjoin
end P2MW
export P2MW.S_ModularCurve_forall_isAffineGeomPlace_mem_iff_isIntegral_adjoin (solution)
