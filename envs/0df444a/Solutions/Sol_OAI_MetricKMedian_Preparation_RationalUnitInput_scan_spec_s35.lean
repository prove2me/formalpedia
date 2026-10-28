-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.RationalUnitInput.scan_spec_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:36:25.775059+00:00
-- url     : https://prove2.me/submissions/6377d380-c7bc-40f8-9156-6ae5b2f43626

import Mathlib
import Definitions.Def_OAIQ035K076
import Theorems.Thm_OAI_MetricKMedian_Preparation_RationalSuppliers_Data_scan_certificate_s35
import Theorems.Thm_OAI_MetricKMedian_Preparation_selected_preparation_outcome_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteJoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

theorem support_joint (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) (z : Ω × Ξ)
    (h : 0 < (joint μ κ).weight z) : 0 < μ.weight z.1 ∧ 0 < (κ z.1).weight z.2 := by
  exact ⟨pos_of_mul_pos_left h ((κ z.1).nonneg z.2), pos_of_mul_pos_right h (μ.nonneg z.1)⟩

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSupplierSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.SparseIntegerLaw
variable {α β : Type}

theorem bindIndexed_contains (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (a : Fin μ.length) (b : Fin (κ a).length) :
    ∃ i : Fin (μ.bindIndexed κ).length, (μ.bindIndexed κ).states[i.val]=(κ a).states[b.val] := by
  let e : (Σ a : Fin μ.length, Fin (κ a).length) ≃ Fin (∑ a, (κ a).length) := finSigmaFinEquiv
  refine ⟨e ⟨a,b⟩,?_⟩
  simp only [bindIndexed,Vector.getElem_ofFn]
  change (fun z : Σ a : Fin μ.length, Fin (κ a).length => (κ z.1).states[z.2.val])
    (e.symm (e ⟨a,b⟩))=_
  rw [e.symm_apply_apply]

end MetricKMedian.SparseIntegerLaw
namespace MetricKMedian.SparsePrepared
open Finset
variable {n m f : ℕ}

theorem contains_encoded (D : Fin m → Finset (Fin n)) (a q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (p : Fin n → ℚ)
    (ha : ∀ e, 0 ≤ a e ∧ a e ≤ 1) (hq : ∀ e, 0 ≤ q e)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ t, 0 < p t) (hm : ∀ t, ∑ i∈P t,y i=p t)
    (b : Fin (SparseOuterLaw.law D a q ha hq).length) (ξ : Fin n → Finset (Fin f))
    (hξ : 0 < (SparseRescaledInner.encodedLaw P y p
      (total D q Δ (SparseOuterLaw.law D a q ha hq).states[b.val])).weight ξ) :
    ∃ i : Fin (law D a q Δ P y p ha hq).length,
      (law D a q Δ P y p ha hq).states[i.val]=
        ((SparseOuterLaw.law D a q ha hq).states[b.val],
          SparseBundleEncoding.decode (SparseRescaledInner.piece P y p
            (total D q Δ (SparseOuterLaw.law D a q ha hq).states[b.val])) ξ) := by
  let ν := SparseOuterLaw.law D a q ha hq
  let K := total D q Δ ν.states[b.val]
  have hK : ∀ t, K t ≤ Δ := total_le _ _ _ _
  obtain ⟨c,_hc,hc⟩ := SparseBundleEncoding.support (SparseRescaledInner.piece P y p K) K Δ
    (fun i t => ⟨SparseRescaledInner.piece_nonnegative P y p K hy hp i t,
      SparseRescaledInner.piece_cap P y p K Δ hy hp hm hK i t⟩)
    (SparseRescaledInner.piece_sum P y p K hp hm) ξ hξ
  obtain ⟨i,hi⟩ := ν.bindIndexed_contains (fun a => kernel D q Δ P y p ν.states[a.val]) b c
  refine ⟨i,hi.trans ?_⟩
  simp only [kernel,SparseIntegerLaw.map,Vector.getElem_map]
  change (ν.states[b.val],(SparseBundles.law (SparseRescaledInner.piece P y p K)).states[c.val])=_
  rw [← hc]

end MetricKMedian.SparsePrepared
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars
variable {f n : ℕ}

theorem coupled_support (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f))
    (p c : Fin n → ℚ) (γ g : ℚ) (Δ : ℕ)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ t, 0 < p t)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (hm : ∀ t, ∑ i ∈ P t, y i=p t) (hc : ∀ t, ∑ i ∈ A t, y i=c t)
    (hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1/8) (hunit : ∀ t, p t+c t=1)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hg : 0 < g) (heven : Even Δ) (hgrid : g*(Δ:ℚ)=1) :
    let L := coupled y P A p c γ g Δ hy hp hP hm hc hc0 hc1 hunit hγ hγ1 hg heven hgrid;
    let μ := SparsePrepared.law (D A) a (q y P A c γ g) Δ P y p a_bounds
      (q_nonneg y P A c γ g hy hc0 hγ.le hg.le);
    ∀ z : L.Ω × (Fin n → Finset (Fin f)), 0 < (L.ν.joint L.κ).weight z →
      ∃ b : Fin μ.length, ∀ i,
        counts y P A c γ g μ.states[b.val] i=physicalCount L z (physicalIndex i) := by
  intro L μ z hz
  have hz' := L.ν.support_joint L.κ z hz
  obtain ⟨b,hb⟩ := SparsePrepared.contains_encoded (D A) a (q y P A c γ g) Δ P y p
    a_bounds (q_nonneg y P A c γ g hy hc0 hγ.le hg.le) hy hp hm z.1 z.2 hz'.2
  refine ⟨b,?_⟩
  intro i
  change counts y P A c γ g (SparsePrepared.law _ _ _ _ _ _ _ _ _).states[b.val] i=_
  rw [hb]
  dsimp only [counts,physicalCount,L,coupled,CoupledLaw.reindexStars,CoupledLaw.castWeights,
    SparsePrepared.coupled,SparseRescaledInner.encodedCount]
  rfl

end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RationalSupplierScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars

namespace Data
variable {f n j : ℕ} {τ : ℝ} (D : Data f n) (qR : FixedBatch.RationalParameters τ)

theorem tables_support (heven : Even qR.Δ)
    (z : (D.coupled qR heven).Ω × (Fin n → Finset (Fin f)))
    (hz : 0 < ((D.coupled qR heven).ν.joint (D.coupled qR heven).κ).weight z) :
    ∃ N ∈ D.tables qR, ∀ a, N a=physicalCount (D.coupled qR heven) z (physicalIndex a) := by
  obtain ⟨b,hb⟩ := coupled_support D.y D.P D.A D.p D.c D.γ qR.g qR.Δ
    D.hy D.hp D.hP D.hm D.hc D.hc0 D.hc1 D.hunit D.hγ D.hγ1
    (FixedParameters.positive qR) heven (FixedParameters.grid qR) z hz
  refine ⟨counts D.y D.P D.A D.c D.γ qR.g (D.law qR).states[b.val],?_,hb⟩
  apply List.mem_map.mpr
  exact ⟨(D.law qR).states[b.val],Vector.mem_toList_iff.mpr (Vector.getElem_mem b.isLt),rfl⟩

theorem scan_feasible {X : Type} [PseudoMetricSpace X]
    (heven : Even qR.Δ) (hτ : τ<1) (hj : 0<j)
    (df : Fin f → Fin f → ℚ) (dc : Fin j → Fin f → ℚ)
    (i : Fin f → X) (client : Fin j → X)
    (hdf : ∀ a b, dist (i a) (i b)=(df a b:ℝ))
    (hdc : ∀ c a, dist (client c) (i a)=(dc c a:ℝ))
    (B : ℚ) (z : (D.coupled qR heven).Ω × (Fin n → Finset (Fin f)))
    (hz : 0 < ((D.coupled qR heven).ν.joint (D.coupled qR heven).κ).weight z)
    (hcap : ∀ a, physicalCount (D.coupled qR heven) z a ≤ qR.Δ)
    (hm : 1 ≤ ∑ a, (qR.g:ℝ)*(physicalCount (D.coupled qR heven) z a:ℝ))
    (hB : (∑ a, (qR.g:ℝ)*(physicalCount (D.coupled qR heven) z a:ℝ))+(qR.allowance:ℝ) ≤ (B:ℝ))
    (r : Fin j → Physical (Fin f) (Fin n) → ℝ)
    (hr : ∀ c, (∀ a, 0 ≤ r c a ∧ r c a ≤ (qR.g:ℝ)*(physicalCount (D.coupled qR heven) z a:ℝ)) ∧
      (∑ a, r c a)=1) :
    ∃ O : Finset (Fin f), D.scan qR df dc B=some O ∧ O.Nonempty ∧
      (O.card:ℝ) ≤ (B:ℝ) ∧
      (Completion.Rational.score dc O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*
        (∑ c,∑ a, r c a*dist (client c) (Sum.elim i (fun ti => i ti.2) a)) := by
  obtain ⟨N,hN,heq⟩ := D.tables_support qR heven z hz
  exact scan_certificate_s35 qR hτ hj df dc i client hdf hdc B (D.tables qR)
    (physicalCount (D.coupled qR heven) z) N hN heq hcap hm hB r hr

end Data
end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalGeometryScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Preparation.RationalBundles
open Finset SupplierStars RationalSuppliers
variable {f n j : ℕ} {X : Type} [PseudoMetricSpace X]

 theorem scan_geometry {τ : ℝ} (qR : FixedBatch.RationalParameters τ)
    (heven : Even qR.Δ) (hτ0 : 0<τ) (hτ : τ<1) (hj : 0<j)
    (F : Fin n → Finset (Fin f)) (Fj : Fin j → Finset (Fin f)) (y : Fin f → ℚ)
    (s : Fin n → X) (i : Fin f → X) (client : Fin j → X)
    (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ)
    (df : Fin f → Fin f → ℚ) (dc : Fin j → Fin f → ℚ)
    (V : Fin n → ℚ) (v : Fin j → ℚ) (rep : Fin j → Fin n) (M δ γ T₁ B : ℚ)
    (hd : ∀ t u, dist (s t) (s u)=(d t u:ℝ))
    (hdi : ∀ t a, dist (s t) (i a)=(di t a:ℝ))
    (hdf : ∀ a b, dist (i a) (i b)=(df a b:ℝ))
    (hdc : ∀ c a, dist (client c) (i a)=(dc c a:ℝ))
    (hy : ∀ a, 0 < y a) (hy1 : ∀ a, y a≤1)
    (hM : 0 < M) (hδ : 0 < δ) (hδ1 : (δ:ℝ) ≤ 1/4)
    (hθ : 1/((M:ℝ)*(δ:ℝ)) ≤ 1/8) (hγ : 0<γ) (hγ1 : γ≤1) (hT : 0<T₁)
    (hα : (M:ℝ)/((δ:ℝ)*(T₁:ℝ)) ≤ 1/4)
    (hfail : failureFactor (γ:ℝ) (qR.g:ℝ)<1)
    (hB : (∑ a, (y a:ℝ))+3*(qR.g:ℝ)+(qR.allowance:ℝ) ≤ (B:ℝ))
    (hu : ∀ t, ∑ a ∈ F t, y a=1)
    (hv : ∀ t, ∑ a ∈ F t, y a*di t a=V t)
    (hju : ∀ c, ∑ a ∈ Fj c, y a=1)
    (hjv : ∀ c, ∑ a ∈ Fj c, y a*dc c a=v c)
    (hs : ∀ t u, t ≠ u → M*max (V t) (V u) < d t u)
    (hnearest : ∀ t, ∀ a ∈ F t, ∀ b ∉ F t, di t a≤di t b)
    (hrepV : ∀ c, V (rep c)≤v c) (hrepD : ∀ c, dist (client c) (s (rep c))≤(M:ℝ)*(v c:ℝ)) :
    let D := suppliers F y s i d di V M δ γ hd hdi hy hM hδ (by linarith only [hδ1]) hθ hγ hγ1 hu hv hs;
    ∃ O : Finset (Fin f), D.scan qR df dc B=some O ∧ O.Nonempty ∧
      (O.card:ℝ)≤(B:ℝ) ∧ (Completion.Rational.score dc O:ℝ) ≤
      ((1+2/Real.exp 1+τ)/(1-τ)) *
      (max (farFactor (δ:ℝ) (1-1/((M:ℝ)*(δ:ℝ))) ((M:ℝ)/((δ:ℝ)*(T₁:ℝ))) ((M:ℝ)/(T₁:ℝ)) (γ:ℝ))
        (nearFactor (1-1/((M:ℝ)*(δ:ℝ))) ((M:ℝ)+(1+(δ:ℝ))*(T₁:ℝ)) (γ:ℝ) (qR.g:ℝ)) /
        (1-failureFactor (γ:ℝ) (qR.g:ℝ)))*(∑ c, (v c:ℝ)) := by
  intro D
  let : Nonempty (Fin j) := ⟨⟨0,hj⟩⟩
  let G := geometry F y s i d di V M δ hd hdi hy hM hδ (by linarith only [hδ1]) hu hv hs
  obtain ⟨z,hz,r,hcap,hm,hbudget,hr,hcost⟩ := selected_preparation_outcome_s35 F Fj
    (fun a => (y a:ℝ)) s client i (fun t => (V t:ℝ)) (fun c => (v c:ℝ)) rep
    (fun a => by exact_mod_cast hy a) (fun a => by exact_mod_cast hy1 a)
    (by exact_mod_cast hM) (by exact_mod_cast hδ) hδ1 (by exact_mod_cast hT) hθ hα
    qR.gpos (by exact_mod_cast hγ) (by exact_mod_cast hγ1) heven qR.unit hfail
    (fun t => by exact_mod_cast hu t) (fun c => by exact_mod_cast hju c)
    (fun t => by simp only [hdi]; exact_mod_cast hv t)
    (fun c => by simp only [hdc]; exact_mod_cast hjv c)
    (fun t a ha b hb => by simp only [hdi]; exact_mod_cast hnearest t a ha b hb)
    (fun t u htu => by simp only [hd]; exact_mod_cast hs t u htu)
    (fun c => by exact_mod_cast hrepV c) hrepD G (D.coupled qR heven)
  obtain ⟨O,hO,hOn,hOc,hOs⟩ := D.scan_feasible qR heven hτ hj df dc i client hdf hdc B
    z hz hcap hm (by
      calc
        _ ≤ ((∑ a, (y a:ℝ))+3*(qR.g:ℝ))+(qR.allowance:ℝ) := add_le_add hbudget le_rfl
        _ ≤ (B:ℝ) := hB) r hr
  refine ⟨O,hO,hOn,hOc,?_⟩
  rw [mul_assoc]
  exact hOs.trans (mul_le_mul_of_nonneg_left hcost (by
    apply div_nonneg _ (by linarith only [hτ])
    positivity))

end MetricKMedian.Preparation.RationalBundles
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalUnitInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Preparation
open Finset

namespace RationalUnitInput
variable {f j : ℕ} (U : RationalUnitInput f j)

theorem representative_cover (M : ℚ) (hM : 0≤M) (c : Fin j) :
    ∃ t, U.V (U.ridx M t)≤U.V c ∧ U.dd c (U.ridx M t)≤M*U.V c := by
  obtain ⟨s,hs,hV,hd⟩ :=
    (RationalRepresentatives.representatives_spec U.dd U.V M U.hdd U.hsymm hM U.V_nonneg).2 c
  let t := ((U.representatives M).orderIsoOfFin rfl).symm ⟨s,hs⟩
  have ht : U.ridx M t=s := congrArg Subtype.val
    (((U.representatives M).orderIsoOfFin rfl).apply_symm_apply ⟨s,hs⟩)
  exact ⟨t,ht ▸ hV,ht ▸ hd⟩

end RationalUnitInput
end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalUnitScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Preparation.RationalUnitInput
open Finset
variable {f j : ℕ} {X : Type} [PseudoMetricSpace X]
variable (U : RationalUnitInput f j) (R : U.Realization X) {η τ : ℝ} (p : RationalAllParameters η τ)

theorem scan_spec_s35_oai (hτ0 : 0<τ) (hτ : τ<1) (hj : 0<j) (B : ℚ)
    (hB : (∑ a, (U.y a:ℝ))+3*(p.round.g:ℝ)+(p.round.allowance:ℝ) ≤ (B:ℝ)) :
    ∃ O : Finset (Fin f), U.scan R p B=some O ∧ O.Nonempty ∧ (O.card:ℝ)≤(B:ℝ) ∧
      (Completion.Rational.score U.dc O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*(1+η)*(∑ c, (U.V c:ℝ)) := by
  classical
  choose rep hV hd using U.representative_cover p.M p.hM.le
  obtain ⟨O,hO,hOn,hOc,hCost⟩ := RationalBundles.scan_geometry p.round p.even hτ0 hτ hj
    (fun t => U.F (U.ridx p.M t)) U.F U.y (fun t => R.c (U.ridx p.M t)) R.i R.c
    (fun t u => U.dd (U.ridx p.M t) (U.ridx p.M u)) (fun t a => U.dc (U.ridx p.M t) a)
    U.df U.dc (fun t => U.V (U.ridx p.M t)) U.V rep p.M p.δ p.γ p.T₁ B
    (fun t u => R.hdd (U.ridx p.M t) (U.ridx p.M u))
    (fun t a => R.hdc (U.ridx p.M t) a) R.hdf R.hdc U.hy U.hy1
    p.hM p.hδ p.hδ1 p.hθ p.hγ p.hγ1 p.hT p.hα p.failure hB
    (fun t => U.hu (U.ridx p.M t)) (fun _ => rfl) U.hu (fun _ => rfl)
    (U.representative_separation p.M p.hM.le)
    (fun t => U.hnear (U.ridx p.M t)) hV
    (fun c => by rw [R.hdd]; exact_mod_cast hd c)
  refine ⟨O,hO,hOn,hOc,hCost.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg (fun c _ => by exact_mod_cast U.V_nonneg c))
  apply mul_le_mul_of_nonneg_left p.error
  exact div_nonneg (by positivity) (by linarith only [hτ])

end MetricKMedian.Preparation.RationalUnitInput
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Preparation.RationalUnitInput.scan_spec_s35_oai := @OAI.MetricKMedian.Preparation.RationalUnitInput.scan_spec_s35_oai
