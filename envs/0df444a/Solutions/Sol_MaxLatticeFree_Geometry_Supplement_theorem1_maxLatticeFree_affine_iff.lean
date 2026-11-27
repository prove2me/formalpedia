-- Prove2me | solution 1 for MaxLatticeFree.Geometry.Supplement.theorem1_maxLatticeFree_affine_iff
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:05:28.438932+00:00
-- url     : https://prove2.me/submissions/16dc4c14-7b7f-43f5-a25a-be9e2f3f93bd

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_LatticeFree
import Definitions.Def_MaxLatticeFree_Geometry_affDim
import Definitions.Def_MaxLatticeFree_Geometry_Polyhedron
import Definitions.Def_MaxLatticeFree_Geometry_Supplement_Rational

open Pointwise
open MaxLatticeFree.Inequalities

open MaxLatticeFree
open MaxLatticeFree.Geometry
open MaxLatticeFree.Geometry.Supplement

theorem solution {n : ℕ} (z : EuclideanSpace ℝ (Fin n))
    (W₀ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (z₀ : EuclideanSpace ℝ (Fin n))
    (hz₀ : z₀ ∈ affSpace z W₀ ∩ integralPoints n) (hW : 0 < Module.finrank ℝ W₀)
    (S : Set (EuclideanSpace ℝ (Fin n))) :
    IsMaximalLatticeFree z W₀ S ↔
      (IsPolyhedronIn ⊤ S ∧ S ⊆ affSpace z W₀ ∧ affDim S = (Module.finrank ℝ W₀ : ℤ) ∧
        IsMaximalLatticeFree z₀ (affHullInt z W₀).direction
          (S ∩ (affHullInt z W₀ : Set (EuclideanSpace ℝ (Fin n)))) ∧
        affDim (S ∩ (affHullInt z W₀ : Set (EuclideanSpace ℝ (Fin n)))) =
          (Module.finrank ℝ (affHullInt z W₀).direction : ℤ) ∧
        (∀ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F →
          IsFacet (S ∩ (affHullInt z W₀ : Set (EuclideanSpace ℝ (Fin n))))
            (F ∩ (affHullInt z W₀ : Set (EuclideanSpace ℝ (Fin n))))) ∧
        (∀ F G : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F → IsFacet S G →
          F ∩ (affHullInt z W₀ : Set (EuclideanSpace ℝ (Fin n))) =
            G ∩ (affHullInt z W₀ : Set (EuclideanSpace ℝ (Fin n))) → F = G) ∧
        (∀ G : Set (EuclideanSpace ℝ (Fin n)),
          IsFacet (S ∩ (affHullInt z W₀ : Set (EuclideanSpace ℝ (Fin n)))) G →
          ∃ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F ∧
            F ∩ (affHullInt z W₀ : Set (EuclideanSpace ℝ (Fin n))) = G)) ∨
      (∃ v ∈ affSpace z W₀, ∃ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)), L ≤ W₀ ∧
        Module.finrank ℝ L + 1 = Module.finrank ℝ W₀ ∧
        S = v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n))) ∧
        Module.finrank ℝ (L ⊓ (affHullInt z W₀).direction :
          Submodule ℝ (EuclideanSpace ℝ (Fin n))) + 1 =
            Module.finrank ℝ (affHullInt z W₀).direction ∧
        ¬ IsRationalSubspace (L ⊓ (affHullInt z W₀).direction)) ∨
      (∃ (a : EuclideanSpace ℝ (Fin n)) (b : ℝ), (∃ w ∈ W₀, inner ℝ a w ≠ 0) ∧
        S = affSpace z W₀ ∩ {x | inner ℝ a x ≤ b} ∧
        (affHullInt z W₀ : Set (EuclideanSpace ℝ (Fin n))) ⊆ {x | inner ℝ a x = b}) := by
          have dimeq : ∀ (S : Set (EuclideanSpace ℝ (Fin n))), S.Nonempty →
              affDim S = (Module.finrank ℝ (vectorSpan ℝ S) : ℤ) := by
            clear * - n
            intro S h
            rw [affDim, if_pos h, direction_affineSpan]
          have lfun : ∀ (m : ℕ), m = n → ∀ {E : Type} [AddCommGroup E] [Module ℝ E]
              (g : E →ₗ[ℝ] ℝ) (x w : E) (t : ℝ), g (x + t • w) = g x + t * g w := by
            clear * - n
            intro m _ E _ _ g x w t
            rw [g.map_add, g.map_smul, smul_eq_mul]
          have lfund : ∀ (m : ℕ), m = n → ∀ {E : Type} [AddCommGroup E] [Module ℝ E]
              (g : E →ₗ[ℝ] ℝ) (x y : E) (t : ℝ), g (x + t • (y - x)) = g x + t * (g y - g x) := by
            clear * - lfun n
            intro m hm E _ _ g x y t
            rw [lfun m hm, g.map_sub]
          have cvxlt : ∀ (m : ℕ), m = n → ∀ (a b c t : ℝ), a < c → b ≤ c → 0 ≤ t → t < 1 →
              a + t * (b - a) < c := by
            clear * - n
            intro m _ a b c t ha hb h0 h1
            have h2 := mul_lt_mul_of_pos_right h1 (sub_pos.mpr ha)
            rw [one_mul] at h2
            exact lt_sub_iff_add_lt'.mp
              ((mul_le_mul_of_nonneg_left (sub_le_sub_right hb a) h0).trans_lt h2)
          have midle : ∀ (m : ℕ), m = n → ∀ (a b c : ℝ), a ≤ c → b ≤ c →
              a + 1 / 2 * (b - a) ≤ c := by
            clear * - n
            intro m _ a b c ha hb
            linarith
          have subW : ∀ (m : ℕ), m = n → ∀ {E : Type} [AddCommGroup E] [Module ℝ E]
              (W : Submodule ℝ E) (z x y : E), x - z ∈ W → y - z ∈ W → x - y ∈ W := by
            clear * - n
            intro m _ E _ _ W z x y hx hy
            have h := W.sub_mem hx hy
            rw [sub_sub_sub_cancel_right] at h
            exact h
          have addW : ∀ (m : ℕ), m = n → ∀ {E : Type} [AddCommGroup E] [Module ℝ E]
              (W : Submodule ℝ E) (z x w : E) (t : ℝ), x - z ∈ W → w ∈ W → x + t • w - z ∈ W := by
            clear * - n
            intro m _ E _ _ W z x w t hx hw
            rw [add_sub_right_comm]
            exact W.add_mem hx (W.smul_mem t hw)
          have spanker : ∀ (m : ℕ), m = n → ∀ {E : Type} [AddCommGroup E] [Module ℝ E]
              (g : E →ₗ[ℝ] ℝ) (b : ℝ) (S : Set E), (∀ x ∈ S, g x = b) → vectorSpan ℝ S ≤ LinearMap.ker g := by
            clear * - n
            intro m _ E _ _ g b S h
            refine Submodule.span_le.mpr ?_
            rintro w ⟨x, hx, y, hy, rfl⟩
            show g (x - y) = 0
            rw [g.map_sub, h x hx, h y hy, sub_self]
          have spanW : ∀ (m : ℕ), m = n → ∀ {E : Type} [AddCommGroup E] [Module ℝ E]
              (W : Submodule ℝ E) (z : E) (S : Set E), (∀ x ∈ S, x - z ∈ W) → vectorSpan ℝ S ≤ W := by
            clear * - subW n
            intro m hm E _ _ W z S h
            refine Submodule.span_le.mpr ?_
            rintro w ⟨x, hx, y, hy, rfl⟩
            exact subW m hm W z x y (h x hx) (h y hy)
          have vseq : ∀ (m : ℕ), m = n → ∀ {E : Type} [AddCommGroup E] [Module ℝ E]
              (z₀ : E) (W : Submodule ℝ E) (S : Set E) (p : E),
              (∀ x ∈ S, x - z₀ ∈ W) → p ∈ S → (∀ w ∈ W, ∃ t : ℝ, 0 < t ∧ p + t • w ∈ S) →
              vectorSpan ℝ S = W := by
            clear * - spanW n
            intro m hm E _ _ z₀ W S p hSA hpS hball
            refine le_antisymm (spanW m hm W z₀ S hSA) fun w hw => ?_
            obtain ⟨t, ht, hy⟩ := hball w hw
            have h2 : (p + t • w) - p ∈ vectorSpan ℝ S := Submodule.subset_span ⟨_, hy, _, hpS, rfl⟩
            rw [add_sub_cancel_left] at h2
            have h3 := (vectorSpan ℝ S).smul_mem t⁻¹ h2
            rw [inv_smul_smul₀ ht.ne'] at h3
            exact h3
          have nudge : ∀ (m : ℕ), m = n → ∀ {E ι : Type} [AddCommGroup E] [Module ℝ E]
              (f : ι → E →ₗ[ℝ] ℝ) (β : ι → ℝ) (x w : E) (T : Finset ι), (∀ c ∈ T, f c x < β c) →
              ∃ t : ℝ, 0 < t ∧ ∀ c ∈ T, f c (x + t • w) < β c := by
            clear * - lfun n
            intro m hm E ι _ _ f β x w T hx
            have h : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), ∀ c ∈ T, f c x + t * f c w < β c := by
              refine (Filter.eventually_all_finset T).mpr fun c hc => ?_
              have h1 : Continuous fun t : ℝ => f c x + t * f c w :=
                continuous_const.add (continuous_id.mul continuous_const)
              refine (h1.continuousAt.eventually_lt continuousAt_const ?_).filter_mono nhdsWithin_le_nhds
              rw [zero_mul, add_zero]
              exact hx c hc
            obtain ⟨t, h1, h2⟩ := (h.and self_mem_nhdsWithin).exists
            exact ⟨t, h2, fun c hc => (lfun m hm (f c) x w t).trans_lt (h1 c hc)⟩
          have strictpt : ∀ (m : ℕ), m = n → ∀ {E ι : Type} [AddCommGroup E] [Module ℝ E]
              (f : ι → E →ₗ[ℝ] ℝ) (β : ι → ℝ) (T : Finset ι) (K : Set E), K.Nonempty →
              (∀ x ∈ K, ∀ y ∈ K, x + (1 / 2 : ℝ) • (y - x) ∈ K) → (∀ c ∈ T, ∀ x ∈ K, f c x ≤ β c) →
              (∀ c ∈ T, ∃ x ∈ K, f c x < β c) → ∃ x ∈ K, ∀ c ∈ T, f c x < β c := by
            clear * - lfund n
            classical
            intro m hm E ι _ _ f β T K hne hmid
            have h1 : ∀ a b c : ℝ, a ≤ c → b ≤ c → (a < c ∨ b < c) → a + 1 / 2 * (b - a) < c := by
              intro a b c ha hb h
              rcases h with h | h <;> linarith
            induction T using Finset.induction_on with
            | empty =>
              intro _ _
              obtain ⟨s, hs⟩ := hne
              exact ⟨s, hs, fun c hc => absurd hc (Finset.notMem_empty c)⟩
            | insert c U hcU ih =>
              intro hle hlt
              obtain ⟨x, hxK, hx⟩ := ih (fun d hd => hle d (Finset.mem_insert_of_mem hd))
                (fun d hd => hlt d (Finset.mem_insert_of_mem hd))
              obtain ⟨y, hyK, hy⟩ := hlt c (Finset.mem_insert_self _ _)
              refine ⟨_, hmid x hxK y hyK, fun d hd => ?_⟩
              rw [lfund m hm]
              refine h1 _ _ _ (hle d hd x hxK) (hle d hd y hyK) ?_
              rcases Finset.mem_insert.mp hd with rfl | hd
              · exact Or.inr hy
              · exact Or.inl (hx d hd)
          have irredcore : ∀ (m : ℕ), m = n → ∀ {E ι : Type} [AddCommGroup E] [Module ℝ E]
              [FiniteDimensional ℝ E] (f : ι → E →ₗ[ℝ] ℝ) (β : ι → ℝ) (z₀ : E) (W : Submodule ℝ E)
              (T : Finset ι) (S : Set E), S.Nonempty → Module.finrank ℝ (vectorSpan ℝ S) = Module.finrank ℝ W →
              (∀ x, x ∈ S ↔ x - z₀ ∈ W ∧ ∀ c ∈ T, f c x ≤ β c) →
              ∃ T' : Finset ι, T' ⊆ T ∧ (∀ x, x ∈ S ↔ x - z₀ ∈ W ∧ ∀ c ∈ T', f c x ≤ β c) ∧
                (∃ p, p - z₀ ∈ W ∧ ∀ c ∈ T', f c p < β c) ∧
                ∀ c ∈ T', ∃ q, q - z₀ ∈ W ∧ f c q = β c ∧ ∀ d ∈ T', d ≠ c → f d q < β d := by
            clear * - lfund cvxlt midle subW addW spanker spanW strictpt n
            classical
            intro m hm E ι _ _ _ f β z₀ W T S hne hdim hS
            have hcomb : ∀ x y : E, ∀ t : ℝ, x - z₀ ∈ W → y - z₀ ∈ W → x + t • (y - x) - z₀ ∈ W :=
              fun x y t hx hy => addW m hm W z₀ x _ t hx (subW m hm W z₀ y x hy hx)
            have hex : ∃ k : ℕ, ∃ U : Finset ι, U ⊆ T ∧
                (∀ x, x ∈ S ↔ x - z₀ ∈ W ∧ ∀ c ∈ U, f c x ≤ β c) ∧ U.card = k := ⟨T.card, T, subset_rfl, hS, rfl⟩
            obtain ⟨T', hT'T, hST', hcard⟩ := Nat.find_spec hex
            have hviol : ∀ c ∈ T', ∃ x, x - z₀ ∈ W ∧ β c < f c x ∧ ∀ d ∈ T', d ≠ c → f d x ≤ β d := by
              intro c hc
              by_contra hcon
              refine Nat.find_min hex (hcard ▸ Finset.card_erase_lt_of_mem hc)
                ⟨T'.erase c, (Finset.erase_subset _ _).trans hT'T, fun x => ?_, rfl⟩
              rw [hST' x]
              refine and_congr_right fun h1 => ⟨fun h2 d hd => h2 d (Finset.mem_of_mem_erase hd), fun h2 => ?_⟩
              have h3 : ∀ d ∈ T', d ≠ c → f d x ≤ β d := fun d hd hdc => h2 d (Finset.mem_erase.mpr ⟨hdc, hd⟩)
              intro d hd
              by_cases hdc : d = c
              · exact not_lt.mp (fun h => hcon ⟨x, h1, hdc ▸ h, h3⟩)
              · exact h3 d hd hdc
            have hle : ∀ c ∈ T', ∀ x ∈ S, f c x ≤ β c := fun c hc x hx => ((hST' x).mp hx).2 c hc
            have hSA : ∀ x ∈ S, x - z₀ ∈ W := fun x hx => ((hST' x).mp hx).1
            have hstrict1 : ∀ c ∈ T', ∃ x ∈ S, f c x < β c := by
              intro c hc
              by_contra hcon
              have hSeq : ∀ x ∈ S, f c x = β c := fun x hx =>
                le_antisymm (hle c hc x hx) (not_lt.mp fun h => hcon ⟨x, hx, h⟩)
              obtain ⟨x', hx'A, hx'c, -⟩ := hviol c hc
              obtain ⟨s, hs⟩ := hne
              have h2 : vectorSpan ℝ S = W :=
                Submodule.eq_of_le_of_finrank_eq (spanW m hm W z₀ S hSA) hdim
              have h3 := subW m hm W z₀ x' s hx'A (hSA s hs)
              rw [← h2] at h3
              have h4 : f c (x' - s) = 0 := spanker m hm (f c) (β c) S hSeq h3
              rw [(f c).map_sub, hSeq s hs] at h4
              exact hx'c.ne' (sub_eq_zero.mp h4)
            obtain ⟨p, hpS, hp⟩ := strictpt m hm f β T' S hne (fun x hx y hy => by
              refine (hST' _).mpr ⟨hcomb x y _ (hSA x hx) (hSA y hy), fun c hc => ?_⟩
              rw [lfund m hm]
              exact midle m hm _ _ _ (hle c hc x hx) (hle c hc y hy)) hle hstrict1
            refine ⟨T', hT'T, hST', ⟨p, hSA p hpS, hp⟩, ?_⟩
            intro c hc
            obtain ⟨x', hx'A, hx'c, hx'd⟩ := hviol c hc
            have hpc := hp c hc
            have hD : 0 < f c x' - f c p := sub_pos.mpr (hpc.trans hx'c)
            obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (β c - f c p) / (f c x' - f c p) := ⟨_, rfl⟩
            have ht0 : 0 ≤ t := ht ▸ (div_pos (sub_pos.mpr hpc) hD).le
            have ht1 : t < 1 := by rw [ht, div_lt_one hD]; exact sub_lt_sub_right hx'c _
            refine ⟨p + t • (x' - p), hcomb p x' t (hSA p hpS) hx'A, ?_, ?_⟩
            · rw [lfund m hm, ht, div_mul_cancel₀ _ hD.ne']
              exact add_sub_cancel _ _
            · intro d hd hdc
              rw [lfund m hm]
              exact cvxlt m hm _ _ _ t (hp d hd) (hx'd d hd hdc) ht0 ht1
          have smallball : ∀ (m : ℕ), m = n → ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (p w : E) (ε : ℝ), 0 < ε →
                ∃ t : ℝ, 0 < t ∧ p + t • w ∈ Metric.ball p ε := by
            clear * - n
            intro m _ E _ _ p w ε hε
            obtain ⟨t, ht, h⟩ := exists_pos_mul_lt hε ‖w‖
            refine ⟨t, ht, mem_ball_iff_norm.mpr ?_⟩
            rw [add_sub_cancel_left]
            refine ((norm_smul t w).trans ?_).trans_lt h
            rw [mul_comm, Real.norm_of_nonneg ht.le]
          have fulldim : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (S : Set (EuclideanSpace ℝ (Fin n))) (p : EuclideanSpace ℝ (Fin n)),
              S ⊆ affSpace z₀ W → p ∈ intRel (affSpace z₀ W) S →
              affDim S = (Module.finrank ℝ W : ℤ) := by
            clear * - dimeq addW vseq smallball n
            intro z₀ W S p hSA hp
            obtain ⟨hpS, ε, hε, hball⟩ := hp
            rw [dimeq S ⟨p, hpS⟩, vseq n rfl z₀ W S p hSA hpS (fun w hw => by
              obtain ⟨t, ht, hb⟩ := smallball n rfl p w ε hε
              exact ⟨t, ht, hball ⟨hb, addW n rfl W z₀ p w t (hSA hpS) hw⟩⟩)]
          have facet_nested : ∀ (S F G : Set (EuclideanSpace ℝ (Fin n))),
              IsFacet S F → IsFacet S G → F ⊆ G → F = G := by
            clear * - dimeq spanker n
            have core : ∀ {E : Type} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
                (F G : Set E) (g : E →ₗ[ℝ] ℝ) (f : E) (b : ℝ), f ∈ F → F ⊆ G →
                Module.finrank ℝ (vectorSpan ℝ F) = Module.finrank ℝ (vectorSpan ℝ G) →
                (∀ x ∈ F, g x = b) → ∀ x ∈ G, g x = b := by
              intro E _ _ _ F G g f b hf hFG hd hFb x hx
              have hV : vectorSpan ℝ F = vectorSpan ℝ G :=
                Submodule.eq_of_le_of_finrank_eq (vectorSpan_mono ℝ hFG) hd
              have h1 : x - f ∈ vectorSpan ℝ G := vsub_mem_vectorSpan ℝ hx (hFG hf)
              rw [← hV] at h1
              have h2 : g (x - f) = 0 := spanker n rfl g b F hFb h1
              rw [g.map_sub, hFb f hf] at h2
              exact sub_eq_zero.mp h2
            intro S F G hF hG hFG
            obtain ⟨⟨f, hf⟩, hdF, a, b, hval, hFeq⟩ := hF
            obtain ⟨hGne, hdG, a', b', hval', hGeq⟩ := hG
            refine Set.Subset.antisymm hFG ?_
            have hd := (dimeq F ⟨f, hf⟩).symm.trans ((hdF.trans hdG.symm).trans (dimeq G hGne))
            have h := core F G (innerₛₗ ℝ a) f b hf hFG (Int.ofNat.inj hd)
              (fun x hx => (Set.ext_iff.mp hFeq x |>.mp hx).2)
            intro x hx
            exact (Set.ext_iff.mp hFeq x).mpr ⟨((Set.ext_iff.mp hGeq x).mp hx).1, h x hx⟩
          have irred : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (T : Finset (EuclideanSpace ℝ (Fin n) × ℝ)) (S : Set (EuclideanSpace ℝ (Fin n))),
              S = affSpace z₀ W ∩ {x | ∀ c ∈ T, inner ℝ c.1 x ≤ c.2} →
              affDim S = (Module.finrank ℝ W : ℤ) →
              ∃ T' : Finset (EuclideanSpace ℝ (Fin n) × ℝ), T' ⊆ T ∧
                S = affSpace z₀ W ∩ {x | ∀ c ∈ T', inner ℝ c.1 x ≤ c.2} ∧
                (∃ p ∈ affSpace z₀ W, ∀ c ∈ T', inner ℝ c.1 p < c.2) ∧
                ∀ c ∈ T', ∃ q ∈ affSpace z₀ W, inner ℝ c.1 q = c.2 ∧
                  ∀ d ∈ T', d ≠ c → inner ℝ d.1 q < d.2 := by
            clear * - dimeq irredcore n
            intro z₀ W T S hS hdim
            have hne : S.Nonempty := by
              by_contra h
              rw [affDim, if_neg h] at hdim
              exact absurd (hdim ▸ Int.natCast_nonneg _ : (0:ℤ) ≤ -1) (by decide)
            rw [dimeq S hne] at hdim
            obtain ⟨T', h1, h2, h3, h4⟩ := irredcore n rfl (fun c : EuclideanSpace ℝ (Fin n) × ℝ => innerₛₗ ℝ c.1)
              Prod.snd z₀ W T S hne (Int.ofNat.inj hdim) (fun x => by rw [hS]; exact Iff.rfl)
            exact ⟨T', h1, Set.ext h2, h3, h4⟩
          have facetcore : ∀ (m : ℕ), m = n → ∀ {E ι : Type} [AddCommGroup E] [Module ℝ E]
              [FiniteDimensional ℝ E] (f : ι → E →ₗ[ℝ] ℝ) (β : ι → ℝ) (z₀ : E) (W : Submodule ℝ E)
              (T : Finset ι) (S : Set E) (p : E),
              (∀ x, x ∈ S ↔ x - z₀ ∈ W ∧ ∀ c ∈ T, f c x ≤ β c) →
              p - z₀ ∈ W → (∀ c ∈ T, f c p < β c) →
              (∀ c ∈ T, ∃ q, q - z₀ ∈ W ∧ f c q = β c ∧ ∀ d ∈ T, d ≠ c → f d q < β d) →
              p ∈ S ∧ vectorSpan ℝ S = W ∧
              (∀ c ∈ T, (S ∩ {x | f c x = β c}).Nonempty ∧
                Module.finrank ℝ (vectorSpan ℝ (S ∩ {x | f c x = β c})) + 1 = Module.finrank ℝ W) ∧
              ∀ (g : E →ₗ[ℝ] ℝ) (b : ℝ), (∀ x ∈ S, g x ≤ b) → (S ∩ {x | g x = b}).Nonempty →
                S ∩ {x | g x = b} ≠ S → ∃ c ∈ T, S ∩ {x | g x = b} ⊆ S ∩ {x | f c x = β c} := by
            clear * - lfun lfund midle subW addW vseq nudge strictpt n
            classical
            intro m hm E ι _ _ _ f β z₀ W T S p hS hpA hp hq
            have hSA : ∀ x ∈ S, x - z₀ ∈ W := fun x hx => ((hS x).mp hx).1
            have hle : ∀ c ∈ T, ∀ x ∈ S, f c x ≤ β c := fun c hc x hx => ((hS x).mp hx).2 c hc
            have hpS : p ∈ S := (hS p).mpr ⟨hpA, fun c hc => (hp c hc).le⟩
            have hnud : ∀ x w : E, x - z₀ ∈ W → w ∈ W → (∀ c ∈ T, f c x < β c) →
                ∃ t : ℝ, 0 < t ∧ x + t • w ∈ S := by
              intro x w hx hw hs
              obtain ⟨t, ht, h⟩ := nudge m hm f β x w T hs
              exact ⟨t, ht, (hS _).mpr ⟨addW m hm W z₀ x w t hx hw, fun c hc => (h c hc).le⟩⟩
            refine ⟨hpS, vseq m hm z₀ W S p hSA hpS (fun w hw => hnud p w hpA hw hp), ?_, ?_⟩
            · intro c hc
              obtain ⟨q, hqA, hqc, hqd⟩ := hq c hc
              have hqS : q ∈ S := by
                refine (hS q).mpr ⟨hqA, fun d hd => ?_⟩
                by_cases h : d = c
                · exact h ▸ hqc.le
                · exact (hqd d hd h).le
              refine ⟨⟨q, hqS, hqc⟩, ?_⟩
              have hV : vectorSpan ℝ (S ∩ {x | f c x = β c}) = W ⊓ LinearMap.ker (f c) := by
                refine vseq m hm q _ _ q ?_ ⟨hqS, hqc⟩ ?_
                · rintro x ⟨hxS, hxc⟩
                  have hxc : f c x = β c := hxc
                  refine ⟨subW m hm W z₀ x q (hSA x hxS) hqA, ?_⟩
                  show f c (x - q) = 0
                  rw [(f c).map_sub, hxc, hqc, sub_self]
                · rintro w ⟨hw, hwc⟩
                  have hwc : f c w = 0 := hwc
                  obtain ⟨t, ht, h⟩ := nudge m hm f β q w (T.erase c)
                    (fun d hd => hqd d (Finset.mem_of_mem_erase hd) (Finset.ne_of_mem_erase hd))
                  have hfc : f c (q + t • w) = β c := by
                    rw [lfun m hm, hwc, mul_zero, add_zero, hqc]
                  refine ⟨t, ht, (hS _).mpr ⟨addW m hm W z₀ q w t hqA hw, fun d hd => ?_⟩, hfc⟩
                  by_cases hdc : d = c
                  · exact hdc ▸ hfc.le
                  · exact (h d (Finset.mem_erase.mpr ⟨hdc, hd⟩)).le
              have hw := subW m hm W z₀ q p hqA hpA
              have hne : (f c).comp W.subtype ≠ 0 := by
                intro h0
                have h1 : f c (q - p) = 0 := LinearMap.congr_fun h0 ⟨q - p, hw⟩
                rw [(f c).map_sub, hqc] at h1
                exact (hp c hc).ne' (sub_eq_zero.mp h1)
              have hrk := LinearMap.finrank_range_add_finrank_ker ((f c).comp W.subtype)
              rw [LinearMap.range_eq_top.mpr (LinearMap.surjective hne), finrank_top, Module.finrank_self,
                LinearMap.ker_comp, ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype,
                add_comm] at hrk
              rw [hV, hrk]
            · intro g b hval hne hneS
              by_contra hcon
              obtain ⟨x, ⟨hxS, hxb⟩, hx⟩ := strictpt m hm f β T (S ∩ {x | g x = b}) hne (by
                rintro x ⟨hx, hxb⟩ y ⟨hy, hyb⟩
                have hxb : g x = b := hxb
                have hyb : g y = b := hyb
                have hw := subW m hm W z₀ y x (hSA y hy) (hSA x hx)
                refine ⟨(hS _).mpr ⟨addW m hm W z₀ x _ _ (hSA x hx) hw, fun c hc => ?_⟩, ?_⟩
                · rw [lfund m hm]
                  exact midle m hm _ _ _ (hle c hc x hx) (hle c hc y hy)
                · show g _ = b
                  rw [lfund m hm, hxb, hyb, sub_self, mul_zero, add_zero])
                (fun c hc x hx => hle c hc x hx.1) (fun c hc => by
                  by_contra h
                  exact hcon ⟨c, hc, fun x hx => ⟨hx.1, le_antisymm (hle c hc x hx.1)
                    (not_lt.mp fun h' => h ⟨x, hx, h'⟩)⟩⟩)
              have hxb : g x = b := hxb
              refine hneS (Set.inter_eq_left.mpr fun y hy => ?_)
              have hw := subW m hm W z₀ x y (hSA x hxS) (hSA y hy)
              obtain ⟨t, ht, h⟩ := hnud x (x - y) (hSA x hxS) hw hx
              have h1 := hval _ h
              rw [lfun m hm, g.map_sub, hxb] at h1
              have h2 := (mul_nonpos_iff_pos_imp_nonpos.mp (add_le_iff_nonpos_right b |>.mp h1)).1 ht
              exact le_antisymm (hval y hy) (sub_nonpos.mp h2)
          have facets : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (T : Finset (EuclideanSpace ℝ (Fin n) × ℝ)) (S : Set (EuclideanSpace ℝ (Fin n))),
              S = affSpace z₀ W ∩ {x | ∀ c ∈ T, inner ℝ c.1 x ≤ c.2} →
              (∃ p ∈ affSpace z₀ W, ∀ c ∈ T, inner ℝ c.1 p < c.2) →
              (∀ c ∈ T, ∃ q ∈ affSpace z₀ W, inner ℝ c.1 q = c.2 ∧
                  ∀ d ∈ T, d ≠ c → inner ℝ d.1 q < d.2) →
              affDim S = (Module.finrank ℝ W : ℤ) ∧
              (∀ c ∈ T, IsFacet S (S ∩ {x | inner ℝ c.1 x = c.2})) ∧
              ∀ F, IsFacet S F → ∃ c ∈ T, F = S ∩ {x | inner ℝ c.1 x = c.2} := by
            clear * - dimeq facet_nested facetcore n
            intro z₀ W T S hS hpex hq
            obtain ⟨p, hpA, hp⟩ := hpex
            obtain ⟨hpS, hV, hF, hG⟩ := facetcore n rfl
              (fun c : EuclideanSpace ℝ (Fin n) × ℝ => innerₛₗ ℝ c.1)
              Prod.snd z₀ W T S p (fun x => by rw [hS]; exact Iff.rfl) hpA hp hq
            have hdimS : affDim S = (Module.finrank ℝ W : ℤ) := by rw [dimeq S ⟨p, hpS⟩, hV]
            have hfac : ∀ c ∈ T, IsFacet S (S ∩ {x | inner ℝ c.1 x = c.2}) := by
              intro c hc
              obtain ⟨h1, h2⟩ := hF c hc
              refine ⟨h1, ?_, c.1, c.2, fun x hx => ((Set.ext_iff.mp hS x).mp hx).2 c hc, rfl⟩
              rw [hdimS, ← h2]
              exact (dimeq _ h1).trans (add_sub_cancel_right (_ : ℤ) 1).symm
            refine ⟨hdimS, hfac, ?_⟩
            intro F hFf
            obtain ⟨hFne, hFd, a, b, hval, hFeq⟩ := id hFf
            obtain ⟨c, hc, hsub⟩ := hG (innerₛₗ ℝ a) b hval (hFeq ▸ hFne) (fun h => by
              have h' : F = S := hFeq.trans h
              rw [h'] at hFd
              exact (sub_one_lt (affDim S)).ne' hFd)
            exact ⟨c, hc, facet_nested S _ _ hFf (hfac c hc) (fun x hx => hsub ((Set.ext_iff.mp hFeq x).mp hx))⟩
          have ir_iff : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (S : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)), x ∈ affSpace z₀ W →
              (x ∈ intRel (affSpace z₀ W) S ↔ ∃ ε : ℝ, 0 < ε ∧ ∀ u ∈ W, ‖u‖ < ε → x + u ∈ S) := by
            clear * - n
            intro z₀ W S x hx
            constructor
            · rintro ⟨hxS, ε, hε, hball⟩
              refine ⟨ε, hε, fun u hu hn => hball ⟨?_, ?_⟩⟩
              · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hn
              · show x + u - z₀ ∈ W
                rw [add_sub_right_comm]; exact W.add_mem hx hu
            · rintro ⟨ε, hε, h⟩
              refine ⟨by rw [← add_zero x]; exact h 0 W.zero_mem (by rw [norm_zero]; exact hε), ε, hε, ?_⟩
              rintro y ⟨hy, hyA⟩
              rw [Metric.mem_ball, dist_eq_norm] at hy
              have := h (y - x) (by rw [← sub_sub_sub_cancel_right y x z₀]; exact W.sub_mem hyA hx) hy
              rwa [add_sub_cancel] at this
          have smallt : ∀ (u : EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0 < ε → ∃ t : ℝ, 0 < t ∧ ‖t • u‖ < ε := by
            clear * - n
            have gen : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : E) (ε : ℝ), 0 < ε →
                ∃ t : ℝ, 0 < t ∧ ‖t • u‖ < ε := by
              intro E _ _ u ε hε
              have hn : 0 < ‖u‖ + 1 := by linarith only [norm_nonneg u]
              refine ⟨ε / (‖u‖ + 1), div_pos hε hn, ?_⟩
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hε hn), div_mul_eq_mul_div, div_lt_iff₀ hn]
              exact mul_lt_mul_of_pos_left (lt_add_one _) hε
            exact fun u ε h => gen _ u ε h
          have intRel_of_strict : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (T : Finset (EuclideanSpace ℝ (Fin n) × ℝ)) (x : EuclideanSpace ℝ (Fin n)),
              x ∈ affSpace z₀ W → (∀ c ∈ T, inner ℝ c.1 x < c.2) →
              x ∈ intRel (affSpace z₀ W) (affSpace z₀ W ∩ {x | ∀ c ∈ T, inner ℝ c.1 x ≤ c.2}) := by
            clear * - n
            intro z₀ W T x hx hT
            refine ⟨⟨hx, fun c hc => (hT c hc).le⟩, ?_⟩
            have hop : IsOpen (⋂ c ∈ T, {y : EuclideanSpace ℝ (Fin n) | inner ℝ c.1 y < c.2}) :=
              isOpen_biInter_finset fun c _ => isOpen_lt (by fun_prop) continuous_const
            obtain ⟨ε, hε, h⟩ := Metric.isOpen_iff.1 hop x (by simpa using hT)
            refine ⟨ε, hε, ?_⟩
            rintro y ⟨hy, hyA⟩
            refine ⟨hyA, fun c hc => ?_⟩
            have := h hy
            simp only [Set.mem_iInter, Set.mem_setOf_eq] at this
            exact (this c hc).le
          have strict_of_intRel : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (S : Set (EuclideanSpace ℝ (Fin n))) (a p x : EuclideanSpace ℝ (Fin n)) (b : ℝ),
              S ⊆ affSpace z₀ W → (∀ x ∈ S, inner ℝ a x ≤ b) → p ∈ affSpace z₀ W → inner ℝ a p < b →
              x ∈ intRel (affSpace z₀ W) S → inner ℝ a x < b := by
            clear * - ir_iff smallt n
            intro z₀ W S a p x b hSA hS hp hpb hx
            have hxA := hSA hx.1
            obtain ⟨ε, hε, h⟩ := (ir_iff z₀ W S x hxA).1 hx
            obtain ⟨t, ht, htn⟩ := smallt (x - p) ε hε
            have hm := hS _ (h (t • (x - p)) (W.smul_mem _ (by
              rw [← sub_sub_sub_cancel_right x p z₀]; exact W.sub_mem hxA hp)) htn)
            rw [inner_add_right, inner_smul_right, inner_sub_right] at hm
            have key : ∀ X P : ℝ, P < b → X + t * (X - P) ≤ b → X < b := by
              intro X P h1 h2
              by_contra hc
              have := mul_pos ht (show 0 < X - P by linarith only [hc, h1])
              linarith only [hc, this, h2]
            exact key _ _ hpb hm
          have aff_poly : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (T : Finset (EuclideanSpace ℝ (Fin n) × ℝ)),
              IsPolyhedronIn ⊤ (affSpace z₀ W ∩ {x | ∀ c ∈ T, inner ℝ c.1 x ≤ c.2}) := by
            clear * - n
            classical
            intro z₀ W T
            have hW : ∃ U : Finset (EuclideanSpace ℝ (Fin n)), ∀ x, x ∈ W ↔ ∀ u ∈ U, inner ℝ u x = 0 := by
              obtain ⟨U, hU⟩ : ∃ U : Finset (EuclideanSpace ℝ (Fin n)), Submodule.span ℝ (U : Set _) = Wᗮ :=
                IsNoetherian.noetherian Wᗮ
              refine ⟨U, fun x => ?_⟩
              rw [← Submodule.orthogonal_orthogonal W, ← hU]
              rw [Submodule.mem_orthogonal]
              constructor
              · intro h u hu
                exact h u (Submodule.subset_span hu)
              · intro h u hu
                induction hu using Submodule.span_induction with
                | mem u hu => exact h u hu
                | zero => simp
                | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
                | smul c a _ ha => rw [real_inner_smul_left, ha, mul_zero]
            obtain ⟨U, hU⟩ := hW
            set T' : Finset (EuclideanSpace ℝ (Fin n) × ℝ) :=
              T ∪ (U.image (fun u => (u, inner ℝ u z₀)) ∪ U.image (fun u => (-u, inner ℝ (-u) z₀))) with hT'
            refine ⟨T'.card, fun i => (T'.equivFin.symm i).1.1, fun i => (T'.equivFin.symm i).1.2, ?_⟩
            have e : affSpace z₀ W ∩ {x | ∀ c ∈ T, inner ℝ c.1 x ≤ c.2} = {x | ∀ c ∈ T', inner ℝ c.1 x ≤ c.2} := by
              ext x
              constructor
              · rintro ⟨hx, hxT⟩ c hc
                have hx' := (hU _).1 hx
                rw [hT', Finset.mem_union, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hc
                rcases hc with hc | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
                · exact hxT c hc
                · have := hx' u hu
                  rw [inner_sub_right] at this
                  show inner ℝ u x ≤ inner ℝ u z₀
                  linarith
                · have := hx' u hu
                  rw [inner_sub_right] at this
                  show inner ℝ (-u) x ≤ inner ℝ (-u) z₀
                  rw [inner_neg_left, inner_neg_left]
                  linarith
              · intro hx
                refine ⟨(hU _).2 fun u hu => ?_, fun c hc => hx c (by rw [hT']; exact Finset.mem_union_left _ hc)⟩
                have h1 := hx (u, inner ℝ u z₀) (by
                  rw [hT']; exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image_of_mem (fun u => (u, inner ℝ u z₀)) hu)))
                have h2 := hx (-u, inner ℝ (-u) z₀) (by
                  rw [hT']; exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun u => (-u, inner ℝ (-u) z₀)) hu)))
                simp only [inner_neg_left] at h1 h2
                rw [inner_sub_right]
                linarith
            rw [e]
            ext x
            simp only [Submodule.top_coe, Set.univ_inter, Set.mem_setOf_eq]
            constructor
            · intro h i
              exact h _ (T'.equivFin.symm i).2
            · intro h c hc
              have := h (T'.equivFin ⟨c, hc⟩)
              simpa using this
          have poly_finset : ∀ (S : Set (EuclideanSpace ℝ (Fin n))), IsPolyhedronIn ⊤ S →
              ∃ T : Finset (EuclideanSpace ℝ (Fin n) × ℝ), S = {x | ∀ c ∈ T, inner ℝ c.1 x ≤ c.2} := by
            clear * - n
            classical
            rintro S ⟨t, a, b, rfl⟩
            refine ⟨Finset.univ.image fun i => (a i, b i), ?_⟩
            ext x
            simp
          have int_transfer : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W D : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (S : Set (EuclideanSpace ℝ (Fin n))) (p x : EuclideanSpace ℝ (Fin n)),
              D ≤ W → Convex ℝ S → p ∈ intRel (affSpace z₀ W) S → p ∈ affSpace z₀ D →
              x ∈ intRel (affSpace z₀ D) (S ∩ affSpace z₀ D) → x ∈ intRel (affSpace z₀ W) S := by
            clear * - ir_iff smallt n
            have gen : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (S : Set E) (p x u : E) (t : ℝ),
                0 < t → Convex ℝ S → x + t • (x - p) ∈ S → p + ((1 + t) / t) • u ∈ S → x + u ∈ S := by
              intro E _ _ S p x u t ht hS h1 h2
              have h1t : 0 < 1 + t := by linarith only [ht]
              have hcomb := hS h1 h2 (a := 1 / (1 + t)) (b := t / (1 + t)) (div_pos one_pos h1t).le
                (div_pos ht h1t).le (by rw [← add_div, div_self h1t.ne'])
              have e : (1 / (1 + t)) • (x + t • (x - p)) + (t / (1 + t)) • (p + ((1 + t) / t) • u) = x + u := by
                match_scalars <;> field_simp <;> ring
              rwa [e] at hcomb
            intro z₀ W D S p x hDW hS hp hpD hx
            have hxD : x ∈ affSpace z₀ D := hx.1.2
            obtain ⟨ε, hε, h⟩ := (ir_iff z₀ D _ x hxD).1 hx
            obtain ⟨δ, hδ, h'⟩ := (ir_iff z₀ W S p (hDW hpD)).1 hp
            obtain ⟨t, ht, htn⟩ := smallt (x - p) ε hε
            have h1 := (h (t • (x - p)) (D.smul_mem _ (by
              rw [← sub_sub_sub_cancel_right x p z₀]; exact D.sub_mem hxD hpD)) htn).1
            have hk : 0 < (1 + t) / t := div_pos (by linarith only [ht]) ht
            refine (ir_iff z₀ W S x (hDW hxD)).2 ⟨δ / ((1 + t) / t), div_pos hδ hk, fun u hu hn => ?_⟩
            refine gen _ S p x u t ht hS h1 (h' _ (W.smul_mem _ hu) ?_)
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk, mul_comm]
            exact (lt_div_iff₀ hk).1 hn
          have affconv : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))),
              Convex ℝ (affSpace z₀ W) := by
            clear * - n
            intro z₀ W x hx y hy s t hs ht hst
            show s • x + t • y - z₀ ∈ W
            have : s • x + t • y - z₀ = s • (x - z₀) + t • (y - z₀) := by
              obtain rfl : t = 1 - s := by linarith
              module
            rw [this]
            exact W.add_mem (W.smul_mem _ hx) (W.smul_mem _ hy)
          have polyconv : ∀ (T : Finset (EuclideanSpace ℝ (Fin n) × ℝ)),
              Convex ℝ {x : EuclideanSpace ℝ (Fin n) | ∀ c ∈ T, inner ℝ c.1 x ≤ c.2} := by
            clear * - n
            intro T x hx y hy s t hs ht hst c hc
            rw [inner_add_right, inner_smul_right, inner_smul_right]
            have h1 := hx c hc
            have h2 := hy c hc
            obtain rfl : t = 1 - s := by linarith
            nlinarith
          have half_lf : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (a : EuclideanSpace ℝ (Fin n)) (b : ℝ), (∃ w ∈ W, inner ℝ a w ≠ 0) →
              (∀ x ∈ affSpace z₀ W, x ∈ integralPoints n → inner ℝ a x = b) →
              IsLatticeFree z₀ W (affSpace z₀ W ∩ {x | inner ℝ a x ≤ b}) := by
            clear * - strict_of_intRel affconv polyconv n
            rintro z₀ W a b ⟨w, hw, haw⟩ hV
            refine ⟨Set.inter_subset_left, (affconv z₀ W).inter ?_, ?_⟩
            · have := polyconv {((a, b) : EuclideanSpace ℝ (Fin n) × ℝ)}
              simpa using this
            · intro x hx hxI
              have hxA := hx.1.1
              obtain ⟨w', hw', haw'⟩ : ∃ w' ∈ W, 0 < inner ℝ a w' := by
                rcases lt_or_gt_of_ne haw with h | h
                · exact ⟨-w, W.neg_mem hw, by rw [inner_neg_right]; linarith⟩
                · exact ⟨w, hw, h⟩
              have hlt := strict_of_intRel z₀ W _ a (x - w') x b Set.inter_subset_left (fun y hy => hy.2) (by
                show x - w' - z₀ ∈ W
                have : x - w' - z₀ = (x - z₀) - w' := by abel
                rw [this]; exact W.sub_mem hxA hw') (by
                rw [inner_sub_right, hV x hxA hxI]; linarith) hx
              rw [hV x hxA hxI] at hlt
              exact lt_irrefl _ hlt
          have lf_of_trace : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W D : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (S B : Set (EuclideanSpace ℝ (Fin n))), D ≤ W →
              (∀ x ∈ affSpace z₀ W, x ∈ integralPoints n → x ∈ affSpace z₀ D) →
              S ⊆ affSpace z₀ W → Convex ℝ S → S ∩ affSpace z₀ D = B → IsLatticeFree z₀ D B →
              IsLatticeFree z₀ W S := by
            clear * - n
            rintro z₀ W D S B hDW hint hSA hconv rfl hB
            refine ⟨hSA, hconv, ?_⟩
            rintro x ⟨hxS, ε, hε, hball⟩ hxI
            have hxD := hint x (hSA hxS) hxI
            refine hB.2.2 x ⟨⟨hxS, hxD⟩, ε, hε, ?_⟩ hxI
            rintro y ⟨hy, hyD⟩
            exact ⟨hball ⟨hy, hDW hyD⟩, hyD⟩
          have trace_lf : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W D : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (S : Set (EuclideanSpace ℝ (Fin n))) (p : EuclideanSpace ℝ (Fin n)), D ≤ W →
              p ∈ intRel (affSpace z₀ W) S → p ∈ affSpace z₀ D → IsLatticeFree z₀ W S →
              IsLatticeFree z₀ D (S ∩ affSpace z₀ D) := by
            clear * - int_transfer affconv n
            intro z₀ W D S p hDW hp hpD hS
            refine ⟨Set.inter_subset_right, hS.2.1.inter (affconv z₀ D), ?_⟩
            intro x hx
            exact hS.2.2 x (int_transfer z₀ W D S p x hDW hS.2.1 hp hpD hx)
          have hbcore : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
              (K : Set E) (p y : E) (D : Submodule ℝ E), Convex ℝ K → p ∈ interior K →
              (∀ d ∈ D, y + d ∉ interior K) →
              ∃ g : E, (∀ x ∈ K, inner ℝ g x ≤ inner ℝ g y) ∧ inner ℝ g p < inner ℝ g y ∧
                ∀ d ∈ D, inner ℝ g d = 0 := by
            clear * - n
            intro E _ _ _ K p y D hK hp hD
            have hdisj : Disjoint (interior K) ((fun x => y + x) '' (D : Set E)) := by
              rw [Set.disjoint_left]
              rintro _ hw ⟨d, hd, rfl⟩
              exact hD d hd hw
            obtain ⟨f, u, hfu, huD⟩ := geometric_hahn_banach_open hK.interior isOpen_interior
              (D.convex.translate y) hdisj
            have huy : u ≤ f y := by
              have h : u ≤ f (y + 0) := huD _ ⟨0, D.zero_mem, rfl⟩
              rwa [add_zero] at h
            have hgf : ∀ w : E, inner ℝ ((InnerProductSpace.toDual ℝ E).symm f) w = f w :=
              fun w => InnerProductSpace.toDual_symm_apply
            have hcl : closure (interior K) ⊆ {w | f w ≤ u} :=
              closure_minimal (fun w hw => (hfu w hw).le) (isClosed_le f.continuous continuous_const)
            have hKcl : K ⊆ closure (interior K) :=
              (hK.closure_interior_eq_closure_of_nonempty_interior ⟨_, hp⟩).symm ▸ subset_closure
            refine ⟨(InnerProductSpace.toDual ℝ E).symm f, fun x hx => ?_, ?_, fun d hd => ?_⟩
            · rw [hgf, hgf]; exact le_trans (hcl (hKcl hx)) huy
            · rw [hgf, hgf]; exact lt_of_lt_of_le (hfu p hp) huy
            · rw [hgf]
              by_contra hne
              have h1 := huD _ ⟨((u - 1 - f y) / f d) • d, D.smul_mem _ hd, rfl⟩
              have h2 : f (y + ((u - 1 - f y) / f d) • d) = u - 1 := by
                rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hne, add_sub_cancel]
              exact absurd (h2 ▸ h1) (not_le.2 (sub_one_lt u))
          have hbint : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
              (W : Submodule ℝ E) (S : Set E) (z : E) (w : W),
              w ∈ interior {w : W | z + (w : E) ∈ S} ↔ 
                (z + (w : E) ∈ S ∧ ∃ ε : ℝ, 0 < ε ∧ Metric.ball (z + (w : E)) ε ∩ {x | x - z ∈ W} ⊆ S) := by
            clear * - n
            intro E _ _ W S z w
            rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
            constructor
            · rintro ⟨ε, hε, hb⟩
              refine ⟨hb (Metric.mem_ball_self hε), ε, hε, ?_⟩
              rintro y ⟨hy, hyA⟩
              have h1 : (⟨y - z, hyA⟩ : W) ∈ Metric.ball w ε := by
                rw [mem_ball_iff_norm] at hy ⊢
                rw [← sub_sub] at hy
                exact hy
              have h3 : z + (y - z) ∈ S := hb h1
              exact (add_sub_cancel z y) ▸ h3
            · rintro ⟨-, ε, hε, hb⟩
              refine ⟨ε, hε, fun u hu => hb ⟨?_, ?_⟩⟩
              · rw [mem_ball_iff_norm] at hu ⊢
                rw [add_sub_add_left_eq_sub]
                exact hu
              · show z + (u : E) - z ∈ W
                rw [add_sub_cancel_left]; exact u.2
          have hbsep : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
              (W D : Submodule ℝ E) (S : Set E) (z p y : E), (∀ x ∈ S, x - z ∈ W) → Convex ℝ S → 
              (p ∈ S ∧ ∃ ε : ℝ, 0 < ε ∧ Metric.ball p ε ∩ {x | x - z ∈ W} ⊆ S) → y - z ∈ W → D ≤ W →
              (∀ x, x - y ∈ D → ¬ (x ∈ S ∧ ∃ ε : ℝ, 0 < ε ∧ Metric.ball x ε ∩ {x | x - z ∈ W} ⊆ S)) →
              ∃ g ∈ W, (∀ x ∈ S, inner ℝ g x ≤ inner ℝ g y) ∧ inner ℝ g p < inner ℝ g y ∧
                ∀ d ∈ D, inner ℝ g d = 0 := by
            clear * - hbcore hbint n
            intro E _ _ _ W D S z p y hSA hconv hp hy hDW hD
            have hpW := hSA p hp.1
            obtain ⟨g, h1, h2, h3⟩ := hbcore {w : W | z + (w : E) ∈ S} ⟨p - z, hpW⟩ ⟨y - z, hy⟩
              (D.comap W.subtype) ((hconv.translate_preimage_right z).linear_preimage W.subtype)
              ((hbint W S z _).2 (by
                show z + (p - z) ∈ S ∧ ∃ ε : ℝ, 0 < ε ∧ Metric.ball (z + (p - z)) ε ∩ {x | x - z ∈ W} ⊆ S
                rw [add_sub_cancel]; exact hp))
              (fun d hd h => hD (y + d) ((add_sub_cancel_left y (d : E)).symm ▸ hd) (by
                have h' := (hbint W S z _).1 h
                have e : z + ((⟨y - z, hy⟩ + d : W) : E) = y + d := by
                  show z + (y - z + (d : E)) = y + d
                  rw [← add_assoc, add_sub_cancel]
                rwa [e] at h'))
            have key : ∀ x, ∀ hx : x - z ∈ W, inner ℝ g (⟨x - z, hx⟩ : W) =
                inner ℝ (g : E) x - inner ℝ (g : E) z := fun x hx => inner_sub_right (g : E) x z
            rw [key p hpW, key y hy] at h2
            refine ⟨g, g.2, fun x hx => ?_, (sub_lt_sub_iff_right _).1 h2, fun d hd => h3 ⟨d, hDW hd⟩ hd⟩
            have h4 := h1 ⟨x - z, hSA x hx⟩ (by
              show z + (x - z) ∈ S
              rw [add_sub_cancel]; exact hx)
            rw [key x (hSA x hx), key y hy] at h4
            exact (sub_le_sub_iff_right _).1 h4
          have hbemp : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
              (K : Set E), Convex ℝ K → interior K = ∅ → 0 < Module.finrank ℝ E →
              ∃ (v : E) (M : Submodule ℝ E), Module.finrank ℝ M + 1 = Module.finrank ℝ E ∧
                ∀ x ∈ K, x - v ∈ M := by
            clear * - n
            intro E _ _ _ K hK hemp hE
            have key : ∃ (v : E) (M : Submodule ℝ E), M < ⊤ ∧ ∀ x ∈ K, x - v ∈ M := by
              rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
              · have : Nontrivial E := Module.finrank_pos_iff.1 hE
                exact ⟨0, ⊥, bot_lt_top, fun x hx => hx.elim⟩
              · refine ⟨x₀, (affineSpan ℝ K).direction, lt_top_iff_ne_top.2 fun h => ?_, fun x hx =>
                  AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ K hx) (subset_affineSpan ℝ K hx₀)⟩
                have h2 := (AffineSubspace.direction_eq_top_iff_of_nonempty
                    ⟨_, subset_affineSpan ℝ K hx₀⟩).1 h
                exact (hK.interior_nonempty_iff_affineSpan_eq_top.2 h2).ne_empty hemp
            obtain ⟨v, M, hM, hSM⟩ := key
            obtain ⟨f, hf0, hfM⟩ := M.exists_le_ker_of_lt_top hM
            refine ⟨v, LinearMap.ker f, ?_, fun x hx => hfM (hSM x hx)⟩
            have h1 := LinearMap.finrank_range_add_finrank_ker f
            rw [LinearMap.range_eq_top.2 (LinearMap.surjective hf0), finrank_top, Module.finrank_self] at h1
            exact (add_comm _ _).trans h1
          have hbempW : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
              (W : Submodule ℝ E) (S : Set E) (z : E), 0 < Module.finrank ℝ W → (∀ x ∈ S, x - z ∈ W) → Convex ℝ S →
              (∀ x, ¬ (x ∈ S ∧ ∃ ε : ℝ, 0 < ε ∧ Metric.ball x ε ∩ {x | x - z ∈ W} ⊆ S)) →
              ∃ v, v - z ∈ W ∧ ∃ L : Submodule ℝ E, L ≤ W ∧ Module.finrank ℝ L + 1 = Module.finrank ℝ W ∧
                ∀ x ∈ S, x - v ∈ L := by
            clear * - hbint hbemp n
            intro E _ _ _ W S z hW hSA hconv hemp
            obtain ⟨v, M, hM, hKM⟩ := hbemp {w : W | z + (w : E) ∈ S}
              ((hconv.translate_preimage_right z).linear_preimage W.subtype)
              (Set.eq_empty_iff_forall_notMem.2 fun w hw => hemp _ ((hbint W S z w).1 hw)) hW
            refine ⟨z + v, (add_sub_cancel_left z (v : E)).symm ▸ v.2, M.map W.subtype,
              Submodule.map_subtype_le _ _, ?_, fun x hx => ?_⟩
            · rw [LinearEquiv.finrank_eq (Submodule.equivSubtypeMap W M).symm]; exact hM
            · refine ⟨_, hKM ⟨x - z, hSA x hx⟩ ?_, ?_⟩
              · show z + (x - z) ∈ S
                rw [add_sub_cancel]; exact hx
              · exact sub_sub x z v
          have hbnoint : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
              (W L : Submodule ℝ E) (z v x : E) (ε : ℝ), L ≤ W → L ≠ W → x - z ∈ W → x - v ∈ L → 0 < ε →
              (∀ y, dist y x < ε → y - z ∈ W → y - v ∈ L) → False := by
            clear * - n
            intro E _ _ W L z v x ε hL hne hx hxL hε h
            obtain ⟨w, hw, hwL⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hL hne)
            have hpos : 0 < ε / (‖w‖ + 1) := div_pos hε (add_pos_of_nonneg_of_pos (norm_nonneg w) one_pos)
            have h1 := h (x + (ε / (‖w‖ + 1)) • w) (by
              rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hpos.le, div_mul_eq_mul_div,
                div_lt_iff₀ (add_pos_of_nonneg_of_pos (norm_nonneg w) one_pos)]
              exact mul_lt_mul_of_pos_left (lt_add_one _) hε)
              (by rw [add_sub_right_comm]; exact W.add_mem hx (W.smul_mem _ hw))
            rw [add_sub_right_comm] at h1
            exact hwL ((L.smul_mem_iff hpos.ne').1 ((L.add_mem_iff_right hxL).1 h1))
          have hyper_lf : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (v : EuclideanSpace ℝ (Fin n)) (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))),
              v ∈ affSpace z₀ W → L ≤ W → Module.finrank ℝ L + 1 = Module.finrank ℝ W →
              IsLatticeFree z₀ W (v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n)))) := by
            clear * - hbnoint n
            intro z₀ W v L hv hL hfin
            have hsub : v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n))) ⊆ affSpace z₀ W := by
              rintro x ⟨l, hl, rfl⟩
              show v + l - z₀ ∈ W
              rw [add_sub_right_comm]; exact W.add_mem hv (hL hl)
            have hmem : ∀ x ∈ v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n))), x - v ∈ L := by
              rintro x ⟨l, hl, rfl⟩
              show v + l - v ∈ L
              rw [add_sub_cancel_left]; exact hl
            refine ⟨hsub, L.convex.vadd v, ?_⟩
            rintro x ⟨hxS, ε, hε, hball⟩ -
            refine hbnoint W L z₀ v x ε hL (fun h => ?_) (hsub hxS) (hmem x hxS) hε
              (fun y hy hyW => hmem y (hball ⟨hy, hyW⟩))
            rw [h] at hfin
            exact Nat.succ_ne_self _ hfin
          have sep_point : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (S : Set (EuclideanSpace ℝ (Fin n))) (p y : EuclideanSpace ℝ (Fin n)),
              S ⊆ affSpace z₀ W → Convex ℝ S → p ∈ intRel (affSpace z₀ W) S → y ∈ affSpace z₀ W →
              y ∉ intRel (affSpace z₀ W) S →
              ∃ a ∈ W, (∀ x ∈ S, inner ℝ a (x - p) ≤ 1) ∧ 1 ≤ inner ℝ a (y - p) := by
            clear * - hbsep n
            intro z₀ W S p y hSA hconv hp hyA hy
            obtain ⟨g, hg, h1, h2, -⟩ := hbsep W ⊥ S z₀ p y hSA hconv hp hyA bot_le
              (fun x hx => by rw [sub_eq_zero.1 ((Submodule.mem_bot ℝ).1 hx)]; exact hy)
            have hδ : 0 < inner ℝ g y - inner ℝ g p := sub_pos.2 h2
            refine ⟨(inner ℝ g y - inner ℝ g p)⁻¹ • g, W.smul_mem _ hg, fun x hx => ?_, ?_⟩
            · rw [real_inner_smul_left, inner_sub_right, inv_mul_le_one₀ hδ]
              exact sub_le_sub_right (h1 x hx) _
            · rw [real_inner_smul_left, inner_sub_right, inv_mul_cancel₀ hδ.ne']
          have hyper_of_empty : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (S : Set (EuclideanSpace ℝ (Fin n))),
              0 < Module.finrank ℝ W → S ⊆ affSpace z₀ W → Convex ℝ S →
              (∀ x, x ∉ intRel (affSpace z₀ W) S) →
              ∃ v ∈ affSpace z₀ W, ∃ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)), L ≤ W ∧
                Module.finrank ℝ L + 1 = Module.finrank ℝ W ∧ S ⊆ v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n))) := by
            clear * - hbempW n
            intro z₀ W S hW hSA hconv hemp
            obtain ⟨v, hv, L, hL, hfin, h⟩ := hbempW W S z₀ hW hSA hconv hemp
            exact ⟨v, hv, L, hL, hfin, fun x hx => ⟨x - v, h x hx, add_sub_cancel v x⟩⟩
          have sep_aff : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W D : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (S : Set (EuclideanSpace ℝ (Fin n))) (p : EuclideanSpace ℝ (Fin n)),
              D ≤ W → S ⊆ affSpace z₀ W → Convex ℝ S → p ∈ intRel (affSpace z₀ W) S →
              (∀ x ∈ affSpace z₀ D, x ∉ intRel (affSpace z₀ W) S) →
              ∃ (a : EuclideanSpace ℝ (Fin n)) (b : ℝ), (∃ w ∈ W, inner ℝ a w ≠ 0) ∧
                (∀ x ∈ S, inner ℝ a x ≤ b) ∧ (∀ x ∈ affSpace z₀ D, inner ℝ a x = b) := by
            clear * - hbsep n
            intro z₀ W D S p hDW hSA hconv hp hdis
            obtain ⟨g, hg, h1, h2, h3⟩ := hbsep W D S z₀ p z₀ hSA hconv hp
              ((sub_self z₀).symm ▸ W.zero_mem) hDW (fun x hx => hdis x hx)
            refine ⟨g, inner ℝ g z₀, ⟨p - z₀, hSA hp.1, ?_⟩, h1, fun x hx => ?_⟩
            · rw [inner_sub_right]; exact (sub_neg.2 h2).ne
            · have := h3 _ hx
              rw [inner_sub_right] at this
              exact sub_eq_zero.1 this
          have c_normal : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
              (L W : Submodule ℝ E) (u : E), L ≤ W → Module.finrank ℝ L + 1 = Module.finrank ℝ W → u ∈ W → u ∉ L →
              ∃ a : E, inner ℝ a u = (1:ℝ) ∧ ∀ w ∈ W, (w ∈ L ↔ inner ℝ a w = (0:ℝ)) := by
            clear * - n
            intro E _ _ _ L W u hLW hfr hu huL
            have h1 := Submodule.finrank_add_inf_finrank_orthogonal hLW
            have h2 : Module.finrank ℝ (Lᗮ ⊓ W : Submodule ℝ E) = 1 :=
              Nat.add_left_cancel (h1.trans hfr.symm)
            haveI : Module.Free ℝ (Lᗮ ⊓ W : Submodule ℝ E) := Module.Free.of_divisionRing ℝ _
            obtain ⟨⟨a, ha⟩, -, hgen⟩ := finrank_eq_one_iff'.mp h2
            have haL : ∀ y ∈ L, inner ℝ a y = (0:ℝ) := (Submodule.mem_orthogonal' L a).mp ha.1
            have key : ∀ w ∈ W, inner ℝ a w = (0:ℝ) → w ∈ L := by
              intro w hw h0
              obtain ⟨y, hy, z, hz, rfl⟩ := L.exists_add_mem_mem_orthogonal w
              have hzW : z ∈ W := (W.add_mem_iff_right (hLW hy)).mp hw
              obtain ⟨c, hc⟩ := hgen ⟨z, hz, hzW⟩
              have hc' : c • a = z := congrArg Subtype.val hc
              rw [inner_add_right, haL y hy, zero_add] at h0
              have hzz : inner ℝ z z = (0:ℝ) := by
                conv_lhs => arg 2; rw [← hc']
                rw [real_inner_smul_left, h0, mul_zero]
              rw [inner_self_eq_zero.mp hzz, add_zero]
              exact hy
            have hne : inner ℝ a u ≠ (0:ℝ) := fun h => huL (key u hu h)
            refine ⟨(inner ℝ a u : ℝ)⁻¹ • a, ?_, fun w hw => ⟨fun hwL => ?_, fun h0 => ?_⟩⟩
            · rw [real_inner_smul_left, inv_mul_cancel₀ hne]
            · rw [real_inner_smul_left, haL w hwL, mul_zero]
            · rw [real_inner_smul_left] at h0
              exact key w hw ((mul_eq_zero.mp h0).resolve_left (inv_ne_zero hne))
          have c_lattice : ∀ (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))), ∃ Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)),
              ∀ x, x ∈ Λ ↔ x ∈ W ∧ x ∈ integralPoints n := by
            clear * - n
            intro W
            refine ⟨{ carrier := {x | x ∈ W ∧ x ∈ integralPoints n}
                      zero_mem' := ⟨W.zero_mem, fun i => ⟨0, Int.cast_zero.symm⟩⟩
                      add_mem' := ?_
                      neg_mem' := ?_ }, fun x => Iff.rfl⟩
            · rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
              refine ⟨W.add_mem hx hy, fun i => ?_⟩
              obtain ⟨p, hp⟩ := hx' i; obtain ⟨q, hq⟩ := hy' i
              exact ⟨p + q, (congrArg₂ (· + ·) hp hq).trans (Int.cast_add p q).symm⟩
            · rintro x ⟨hx, hx'⟩
              refine ⟨W.neg_mem hx, fun i => ?_⟩
              obtain ⟨p, hp⟩ := hx' i
              exact ⟨-p, (congrArg Neg.neg hp).trans (Int.cast_neg p).symm⟩
          have c_dense : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
              (Λ : AddSubgroup E) (a : E),
              (∀ lo hi : ℝ, lo < hi → ∃ l ∈ Λ, lo < inner ℝ a l ∧ inner ℝ a l < hi) ∨
              ∃ l₀ ∈ Λ, ∀ l ∈ Λ, ∃ k : ℤ, inner ℝ a l = (k : ℝ) * inner ℝ a l₀ := by
            clear * - n
            intro E _ _ Λ a
            let φ : E →+ ℝ := AddMonoidHom.mk' (fun x => inner ℝ a x) (fun x y => inner_add_right a x y)
            rcases (Λ.map φ).dense_or_cyclic with hd | ⟨g, hg⟩
            · left
              intro lo hi h
              obtain ⟨r, ⟨l, hl, hlr⟩, h1, h2⟩ := hd.exists_between h
              exact ⟨l, hl, h1.trans_eq hlr.symm, (Eq.trans_lt hlr h2)⟩
            · right
              have hgG : g ∈ Λ.map φ := hg ▸ AddSubgroup.subset_closure rfl
              obtain ⟨l₀, hl₀, hl₀g⟩ := hgG
              refine ⟨l₀, hl₀, fun l hl => ?_⟩
              have : φ l ∈ Λ.map φ := ⟨l, hl, rfl⟩
              rw [hg, AddSubgroup.mem_closure_singleton] at this
              obtain ⟨k, hk⟩ := this
              refine ⟨k, hk.symm.trans ((zsmul_eq_mul g k).trans ?_)⟩
              exact congrArg (fun r => (k:ℝ) * r) hl₀g.symm
          have caseb_rev : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W D L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (v : EuclideanSpace ℝ (Fin n)), z₀ ∈ integralPoints n →
              D = Submodule.span ℝ ((W : Set (EuclideanSpace ℝ (Fin n))) ∩ integralPoints n) →
              v ∈ affSpace z₀ W → L ≤ W → Module.finrank ℝ L + 1 = Module.finrank ℝ W →
              Module.finrank ℝ (L ⊓ D : Submodule ℝ (EuclideanSpace ℝ (Fin n))) + 1 = Module.finrank ℝ D →
              ¬ IsRationalSubspace (L ⊓ D) →
              IsMaximalLatticeFree z₀ W (v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n)))) := by
            clear * - hyper_lf c_normal c_lattice c_dense n
            intro z₀ W D L v hz₀ hD hv hLW hfr hfrD hnr
            -- rationality from cyclicity, in generic form
            have hcyc : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (Λ : AddSubgroup E) (I : Set E)
                (L D : Submodule ℝ E) (a l₀ : E), l₀ ∈ Λ → (Λ : Set E) ⊆ I → D = Submodule.span ℝ (Λ : Set E) →
                (∀ l ∈ D, (l ∈ L ↔ inner ℝ a l = (0:ℝ))) → ¬ D ≤ L →
                (∀ l ∈ Λ, ∃ k : ℤ, inner ℝ a l = (k : ℝ) * inner ℝ a l₀) →
                Submodule.span ℝ (((L ⊓ D : Submodule ℝ E) : Set E) ∩ I) = L ⊓ D := by
              intro E _ _ Λ I L D a l₀ hl₀ hI hD haL hDL hk
              have hΛD : ∀ l ∈ Λ, l ∈ D := fun l hl => hD ▸ Submodule.subset_span hl
              have hg0 : inner ℝ a l₀ ≠ (0:ℝ) := by
                intro h
                apply hDL
                intro l hl
                have hle : Submodule.span ℝ (Λ : Set E) ≤ L := Submodule.span_le.mpr fun l hl => by
                  obtain ⟨k, hk⟩ := hk l hl
                  exact (haL l (hΛD l hl)).mpr (by rw [hk, h, mul_zero])
                exact hle (hD ▸ hl)
              have hMle : Submodule.span ℝ (((L ⊓ D : Submodule ℝ E) : Set E) ∩ I) ≤ L ⊓ D :=
                Submodule.span_le.mpr Set.inter_subset_left
              refine le_antisymm hMle ?_
              intro y hy
              have hDle : Submodule.span ℝ (Λ : Set E) ≤ Submodule.span ℝ (((L ⊓ D : Submodule ℝ E) : Set E) ∩ I) ⊔
                  Submodule.span ℝ {l₀} := by
                rw [Submodule.span_le]
                intro l hl
                obtain ⟨k, hk⟩ := hk l hl
                have hmΛ : l - k • l₀ ∈ Λ := Λ.sub_mem hl (Λ.zsmul_mem hl₀ k)
                have hmL : l - k • l₀ ∈ L := by
                  rw [haL _ (hΛD _ hmΛ), ← Int.cast_smul_eq_zsmul ℝ, inner_sub_right, real_inner_smul_right, hk, sub_self]
                have e : l = (l - k • l₀) + (k : ℝ) • l₀ := by
                  rw [Int.cast_smul_eq_zsmul, sub_add_cancel]
                rw [e]
                exact Submodule.add_mem_sup (Submodule.subset_span ⟨⟨hmL, hΛD _ hmΛ⟩, hI hmΛ⟩)
                  (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
              obtain ⟨m, hm, q, hq, hmq⟩ := Submodule.mem_sup.mp (hDle (hD ▸ hy.2))
              obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hq
              have hmL := hMle hm
              have h1 := (haL y hy.2).mp hy.1
              rw [← hmq, inner_add_right, (haL m hmL.2).mp hmL.1, real_inner_smul_right, zero_add] at h1
              rw [← hmq, (mul_eq_zero.mp h1).resolve_right hg0, zero_smul, add_zero]
              exact hm
            -- convexity, in generic form
            have hcvx : ∀ (E : Type) [AddCommGroup E] [Module ℝ E] (S : Set E) (L : Submodule ℝ E) (v x y : E) (t : ℝ),
                Convex ℝ S → (∀ l ∈ L, v + l ∈ S) → x ∈ S → 0 < t → t < 1 → (y - v) - t • (x - v) ∈ L → y ∈ S := by
              intro E _ _ S L v x y t hS hL hx h0 h1 hl
              have h1t : 0 < 1 - t := sub_pos.mpr h1
              have h := hS (hL _ (L.smul_mem (1 - t)⁻¹ hl)) hx h1t.le h0.le (sub_add_cancel 1 t)
              have e : (1 - t) • (v + (1 - t)⁻¹ • ((y - v) - t • (x - v))) + t • x = y := by
                rw [smul_add, smul_inv_smul₀ h1t.ne', sub_smul, one_smul, smul_sub]
                abel
              exact e ▸ h
            have hin : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a y v u : E), inner ℝ a u = (1:ℝ) →
                inner ℝ a ((y - v) - ((inner ℝ a y : ℝ) - inner ℝ a v) • u) = (0:ℝ) := fun E _ _ a y v u h => by
              rw [inner_sub_right, inner_sub_right, real_inner_smul_right, h, mul_one, sub_self]
            have hadd : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a z l : E) (c : ℝ),
                c - inner ℝ a z < inner ℝ a l → inner ℝ a l < c - inner ℝ a z + 1 →
                c < inner ℝ a (z + l) ∧ inner ℝ a (z + l) < c + 1 := fun E _ _ a z l c h1 h2 => by
              rw [inner_add_right]; exact ⟨sub_lt_iff_lt_add'.mp h1, lt_of_lt_of_eq (add_lt_add_right h2 _) ((add_assoc _ _ _).symm.trans (congrArg (· + 1) (add_sub_cancel _ _)))⟩
            have hopn : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a x : E) (lo hi : ℝ),
                lo < inner ℝ a x → inner ℝ a x < hi → ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ Metric.ball x ε, lo < inner ℝ a y ∧ inner ℝ a y < hi := by
              intro E _ _ a x lo hi h1 h2
              have hopen : IsOpen ((fun y : E => (inner ℝ a y : ℝ)) ⁻¹' Set.Ioo lo hi) :=
                isOpen_Ioo.preimage (continuous_const.inner continuous_id)
              exact Metric.isOpen_iff.mp hopen x ⟨h1, h2⟩
            refine ⟨hyper_lf z₀ W v L hv hLW hfr, fun S' hS' hHS => Set.Subset.antisymm (fun x hx => ?_) hHS⟩
            by_contra hxH
            have hdW : ∀ y ∈ affSpace z₀ W, y - v ∈ W := fun y hy => sub_sub_sub_cancel_right y v z₀ ▸ W.sub_mem hy hv
            have huW := hdW x (hS'.1 hx)
            have huL : x - v ∉ L := fun h => hxH ⟨x - v, h, add_sub_cancel v x⟩
            obtain ⟨a, hau, haL⟩ := c_normal _ L W (x - v) hLW hfr huW huL
            obtain ⟨Λ, hΛ⟩ := c_lattice W
            have hΛe : (Λ : Set (EuclideanSpace ℝ (Fin n))) = (W : Set (EuclideanSpace ℝ (Fin n))) ∩ integralPoints n :=
              Set.ext hΛ
            rcases c_dense _ Λ a with hdense | ⟨l₀, hl₀, hk⟩
            · obtain ⟨l, hl, h1, h2⟩ := hdense (inner ℝ a v - inner ℝ a z₀) (inner ℝ a v - inner ℝ a z₀ + 1) (lt_add_one _)
              have hl' := (hΛ l).mp hl
              have hmem : ∀ y' ∈ affSpace z₀ W, inner ℝ a v < inner ℝ a y' → inner ℝ a y' < inner ℝ a v + 1 → y' ∈ S' := by
                intro y' hy' h1 h2
                refine hcvx _ S' L v x y' (inner ℝ a y' - inner ℝ a v) hS'.2.1 (fun l hl => hHS ⟨l, hl, rfl⟩) hx
                  (sub_pos.mpr h1) (sub_lt_iff_lt_add'.mpr h2) ?_
                exact (haL _ (W.sub_mem (hdW y' hy') (W.smul_mem _ huW))).mpr (hin _ a _ _ _ hau)
              have hyA : z₀ + l ∈ affSpace z₀ W := (congrArg (· ∈ W) (add_sub_cancel_left z₀ l)).mpr hl'.1
              obtain ⟨h3, h4⟩ := hadd _ a z₀ l _ h1 h2
              obtain ⟨ε, hε, hb⟩ := hopn _ a (z₀ + l) _ _ h3 h4
              refine hS'.2.2 (z₀ + l) ⟨hmem _ hyA h3 h4, ε, hε, fun y' hy' => hmem y' hy'.2 (hb y' hy'.1).1 (hb y' hy'.1).2⟩ ?_
              intro i
              obtain ⟨p, hp⟩ := hz₀ i; obtain ⟨q, hq⟩ := hl'.2 i
              exact ⟨p + q, (congrArg₂ (· + ·) hp hq).trans (Int.cast_add p q).symm⟩
            · have hDW : D ≤ W := hD ▸ Submodule.span_le.mpr Set.inter_subset_left
              refine hnr (hcyc _ Λ (integralPoints n) L D a l₀ hl₀ (fun l hl => ((hΛ l).mp hl).2) (hΛe ▸ hD)
                (fun l hl => haL l (hDW hl)) (fun hDL => ?_) hk)
              exact Nat.succ_ne_self _ ((congrArg (fun M : Submodule ℝ (EuclideanSpace ℝ (Fin n)) => Module.finrank ℝ M + 1)
                (inf_eq_right.mpr hDL).symm).trans hfrD)
          have caseb_fwd : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W D L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (v : EuclideanSpace ℝ (Fin n)), z₀ ∈ integralPoints n →
              D = Submodule.span ℝ ((W : Set (EuclideanSpace ℝ (Fin n))) ∩ integralPoints n) →
              v ∈ affSpace z₀ W → L ≤ W → Module.finrank ℝ L + 1 = Module.finrank ℝ W →
              IsMaximalLatticeFree z₀ W (v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n)))) →
              Module.finrank ℝ (L ⊓ D : Submodule ℝ (EuclideanSpace ℝ (Fin n))) + 1 = Module.finrank ℝ D ∧
              ¬ IsRationalSubspace (L ⊓ D) := by
            clear * - strict_of_intRel affconv c_normal c_lattice c_dense n
            intro z₀ W D L v hz₀ hD hv hLW hfr hmax
            -- discreteness, in generic form
            have hdisc : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
                (Λ : AddSubgroup E) (I : Set E)
                (M : Submodule ℝ E) (a l₁ : E), l₁ ∈ Λ → inner ℝ a l₁ ≠ (0:ℝ) → (Λ : Set E) ⊆ I →
                (∀ l ∈ Λ, ∀ t : ℝ, inner ℝ a (l - t • l₁) = (0:ℝ) → l - t • l₁ ∈ M) →
                (∀ m ∈ M, inner ℝ a m = (0:ℝ)) → (∀ m ∈ M, m ∈ I → m ∈ Λ) →
                (∀ R : ℝ, {x : E | x ∈ I ∧ ‖x‖ ≤ R}.Finite) →
                Submodule.span ℝ ((M : Set E) ∩ I) = M →
                (∀ lo hi : ℝ, lo < hi → ∃ l ∈ Λ, lo < inner ℝ a l ∧ inner ℝ a l < hi) → False := by
              intro E _ _ _ Λ I M a l₁ hl₁ hl₁0 hΛI hΛM hM hMΛ hfinI hspan hdense
              obtain ⟨f, hf, hfs, -⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ ((M : Set E) ∩ I)
              replace hfs := hfs.trans hspan
              have hfΛ : ∀ i, f i ∈ Λ := fun i => hMΛ _ (hf i).1 (hf i).2
              set R : ℝ := ‖l₁‖ / |inner ℝ a l₁| + ∑ i, ‖f i‖ with hR
              have hfin2 : (Set.Ioo (0:ℝ) 1 ∩ {r | ∃ l ∈ Λ, inner ℝ a l = r}).Finite := by
                refine ((hfinI R).image (fun x => (inner ℝ a x : ℝ))).subset ?_
                rintro r ⟨⟨hr0, hr1⟩, l, hl, hlr⟩
                have hin : l - (r / inner ℝ a l₁) • l₁ ∈ M := hΛM l hl _ (by
                  rw [inner_sub_right, real_inner_smul_right, hlr, div_mul_cancel₀ _ hl₁0, sub_self])
                rw [← hfs] at hin
                obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hin
                have hsΛ : ∑ i, ⌊w i⌋ • f i ∈ Λ := Λ.sum_mem fun i _ => Λ.zsmul_mem (hfΛ i) _
                have hsM : ∑ i, ⌊w i⌋ • f i ∈ M := M.sum_mem fun i _ => M.toAddSubgroup.zsmul_mem (hf i).1 _
                refine ⟨l - ∑ i, ⌊w i⌋ • f i, ⟨hΛI (Λ.sub_mem hl hsΛ), ?_⟩, ?_⟩
                · have e : l - ∑ i, ⌊w i⌋ • f i = (l - (r / inner ℝ a l₁) • l₁ - ∑ i, ⌊w i⌋ • f i) + (r / inner ℝ a l₁) • l₁ := by
                    rw [sub_right_comm, sub_add_cancel]
                  refine (congrArg norm e).trans_le ((norm_add_le _ _).trans ((add_comm _ _).trans_le (add_le_add ?_ ?_)))
                  · rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hr0, div_mul_eq_mul_div]
                    exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) hr1.le) (abs_nonneg _)
                  · rw [← hw, ← Finset.sum_sub_distrib]
                    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
                    rw [← Int.cast_smul_eq_zsmul ℝ, ← sub_smul, norm_smul, Real.norm_eq_abs, Int.self_sub_floor,
                      abs_of_nonneg (Int.fract_nonneg _)]
                    exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le
                · show inner ℝ a (l - ∑ i, ⌊w i⌋ • f i) = r
                  rw [inner_sub_right, hM _ hsM, hlr, sub_zero]
              have hmulti : Dense {r : ℝ | ∃ l ∈ Λ, inner ℝ a l = r} := dense_of_exists_between fun _ _ hab => by
                obtain ⟨l, hl, h1, h2⟩ := hdense _ _ hab
                exact ⟨_, ⟨l, hl, rfl⟩, h1, h2⟩
              have hsub := hmulti.open_subset_closure_inter (isOpen_Ioo (a := (0:ℝ)) (b := 1))
              rw [hfin2.isClosed.closure_eq] at hsub
              exact (Set.Ioo_infinite one_pos) (hfin2.subset hsub)
            have hrank : ∀ (E : Type) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] (L D W : Submodule ℝ E), L ≤ W →
                D ≤ W → ¬ D ≤ L → Module.finrank ℝ L + 1 = Module.finrank ℝ W →
                Module.finrank ℝ (L ⊓ D : Submodule ℝ E) + 1 = Module.finrank ℝ D := by
              intro E _ _ _ L D W hLW hDW hDL hfr
              have h1 := Submodule.finrank_sup_add_finrank_inf_eq L D
              have h2 := Submodule.finrank_mono (sup_le hLW hDW)
              have h3 := Submodule.finrank_lt_finrank_of_lt (left_lt_sup.mpr hDL)
              have h4 := le_antisymm h2 (hfr.symm.trans_le (Nat.succ_le_of_lt h3))
              rw [h4, ← hfr, add_right_comm] at h1
              exact (add_comm _ 1).trans (Nat.add_left_cancel ((add_left_comm _ _ _).trans ((add_comm _ _).trans h1)))
            have hgap0 : ∀ g b c : ℝ, 0 < g → ∃ lo hi : ℝ, lo < hi ∧ lo ≤ c ∧ c ≤ hi ∧
                ∀ (m : ℤ) (y : ℝ), y - b = m * g → ¬ (lo < y ∧ y < hi) := by
              intro g b c hg
              have h1 := (le_div_iff₀ hg).mp (Int.floor_le ((c - b) / g))
              have h2 := (div_lt_iff₀ hg).mp (Int.lt_floor_add_one ((c - b) / g))
              refine ⟨b + ⌊(c - b) / g⌋ * g, b + (⌊(c - b) / g⌋ + 1) * g,
                add_lt_add_right (mul_lt_mul_of_pos_right (lt_add_one _) hg) _, add_le_of_le_sub_left h1,
                sub_le_iff_le_add'.mp h2.le, ?_⟩
              rintro m y hm ⟨hy1, hy2⟩
              have h3 := lt_of_mul_lt_mul_right ((lt_sub_iff_add_lt'.mpr hy1).trans_eq hm) hg.le
              have h4 := lt_of_mul_lt_mul_right (hm.symm.trans_lt (sub_lt_iff_lt_add'.mpr hy2)) hg.le
              exact absurd (Int.cast_lt.mp h3) (not_lt.mpr (Int.lt_add_one_iff.mp (Int.cast_lt.mp
                (h4.trans_eq ((congrArg (fun r : ℝ => _ + r) Int.cast_one.symm).trans (Int.cast_add _ 1).symm)))))
            have hgap : ∀ g b c : ℝ, g ≠ 0 → ∃ lo hi : ℝ, lo < hi ∧ lo ≤ c ∧ c ≤ hi ∧
                ∀ (m : ℤ) (y : ℝ), y - b = m * g → ¬ (lo < y ∧ y < hi) := by
              intro g b c hg
              rcases lt_or_gt_of_ne hg with h | h
              · obtain ⟨lo, hi, h1, h2, h3, h4⟩ := hgap0 (-g) b c (neg_pos.mpr h)
                exact ⟨lo, hi, h1, h2, h3, fun m y hm => h4 (-m) y (by rw [hm, Int.cast_neg, neg_mul_neg])⟩
              · exact hgap0 g b c h
            have hfinI : ∀ R : ℝ, {x : EuclideanSpace ℝ (Fin n) | x ∈ integralPoints n ∧ ‖x‖ ≤ R}.Finite := by
              intro R
              refine ((Set.finite_Icc (fun _ : Fin n => -⌈R⌉) (fun _ => ⌈R⌉)).image
                (fun m : Fin n → ℤ => (WithLp.toLp 2 (fun i => (m i : ℝ)) : EuclideanSpace ℝ (Fin n)))).subset ?_
              rintro x ⟨hxZ, hxR⟩
              choose m hm using hxZ
              have hb : ∀ i, |(m i : ℝ)| ≤ R := fun i => by
                have h1 : ‖x.ofLp i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
                rw [hm i, Real.norm_eq_abs] at h1
                exact h1.trans hxR
              refine ⟨m, ⟨fun i => ?_, fun i => ?_⟩, ?_⟩
              · have h3 : (-(m i) : ℤ) ≤ ⌈R⌉ := Int.cast_le.mp ((Int.cast_neg (R := ℝ) (m i)).trans_le
                  ((neg_le_abs _).trans ((hb i).trans (Int.le_ceil R))))
                exact neg_le.mp h3
              · exact Int.cast_le.mp ((le_abs_self _).trans ((hb i).trans (Int.le_ceil R)))
              · exact congrArg (WithLp.toLp 2) (funext fun i => (hm i).symm)
            have hconvI : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a : E) (lo hi : ℝ),
                Convex ℝ {x : E | lo ≤ inner ℝ a x ∧ inner ℝ a x ≤ hi} := fun E _ _ a lo hi =>
              (convex_Icc lo hi).is_linear_preimage
                ⟨fun x y => inner_add_right a x y, fun c x => real_inner_smul_right a x c⟩
            have hval : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a u v : E) (d : ℝ),
                inner ℝ a u = (1:ℝ) → inner ℝ a (v + (d - inner ℝ a v) • u) = d := fun E _ _ a u v d h => by
              rw [inner_add_right, real_inner_smul_right, h, mul_one, add_sub_cancel]
            have hval0 : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a l v : E),
                inner ℝ a l = (0:ℝ) → inner ℝ a (v + l) = (inner ℝ a v : ℝ) := fun E _ _ a l v h => by
              rw [inner_add_right, h, add_zero]
            have hsubi : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a x y : E),
                inner ℝ a (x - y) = (inner ℝ a x : ℝ) - inner ℝ a y := fun E _ _ a x y => inner_sub_right a x y
            have hlt : L < W := lt_of_le_of_ne hLW fun h => by
              rw [h] at hfr; exact Nat.succ_ne_self _ hfr
            obtain ⟨u, hu, huL⟩ := SetLike.exists_of_lt hlt
            obtain ⟨a, hau, haL⟩ := c_normal _ L W u hLW hfr hu huL
            obtain ⟨Λ, hΛ⟩ := c_lattice W
            have hΛD : ∀ l ∈ Λ, l ∈ D := fun l hl => hD ▸ Submodule.subset_span ((hΛ l).mp hl)
            have hadd : ∀ l ∈ W, v + l ∈ affSpace z₀ W := fun l hl =>
              (congrArg (· ∈ W) (add_sub_right_comm v l z₀)).mpr (W.add_mem hv hl)
            have hdiff : ∀ y ∈ affSpace z₀ W, y ∈ integralPoints n → y - z₀ ∈ Λ := by
              intro y hy hyZ
              refine (hΛ _).mpr ⟨hy, fun i => ?_⟩
              obtain ⟨p, hp⟩ := hyZ i; obtain ⟨q, hq⟩ := hz₀ i
              exact ⟨p - q, (congrArg₂ (· - ·) hp hq).trans (Int.cast_sub p q).symm⟩
            have hslab : ∀ lo hi : ℝ, lo < hi → lo ≤ inner ℝ a v → inner ℝ a v ≤ hi →
                (∀ y ∈ affSpace z₀ W, y ∈ integralPoints n → ¬ (lo < inner ℝ a y ∧ inner ℝ a y < hi)) → False := by
              intro lo hi hlh hlc hch hno
              have hP : ∀ d : ℝ, v + (d - inner ℝ a v) • u ∈ affSpace z₀ W := fun d => hadd _ (W.smul_mem _ hu)
              have hLF : IsLatticeFree z₀ W (affSpace z₀ W ∩ {x | lo ≤ inner ℝ a x ∧ inner ℝ a x ≤ hi}) := by
                refine ⟨Set.inter_subset_left, (affconv z₀ W).inter (hconvI _ a lo hi), ?_⟩
                intro x hx hxZ
                refine hno x hx.1.1 hxZ ⟨neg_lt_neg_iff.mp ?_, ?_⟩
                · rw [← inner_neg_left]
                  refine strict_of_intRel z₀ W _ (-a) _ x (-lo) Set.inter_subset_left (fun y hy => ?_) (hP hi) ?_ hx
                  · rw [inner_neg_left]; exact neg_le_neg hy.2.1
                  · rw [inner_neg_left, hval _ a u v hi hau]; exact neg_lt_neg hlh
                · refine strict_of_intRel z₀ W _ a _ x hi Set.inter_subset_left (fun y hy => hy.2.2) (hP lo) ?_ hx
                  exact (hval _ a u v lo hau).trans_lt hlh
              have hsub : v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n))) ⊆
                  affSpace z₀ W ∩ {x | lo ≤ inner ℝ a x ∧ inner ℝ a x ≤ hi} := by
                rintro _ ⟨l, hl, rfl⟩
                have h0 := hval0 _ a l v ((haL l (hLW hl)).mp hl)
                exact ⟨hadd l (hLW hl), hlc.trans_eq h0.symm, h0.trans_le hch⟩
              have heq := hmax.2 _ hLF hsub
              have key : ∀ d : ℝ, lo ≤ d → d ≤ hi → d = inner ℝ a v := by
                intro d hd1 hd2
                have hin := hval _ a u v d hau
                have h3 : v + (d - inner ℝ a v) • u ∈ v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n))) :=
                  heq.subset ⟨hP d, hd1.trans_eq hin.symm, hin.trans_le hd2⟩
                obtain ⟨l, hl, hl'⟩ := h3
                rw [← hin, ← hl']
                exact hval0 _ a l v ((haL l (hLW hl)).mp hl)
              exact hlh.ne ((key lo le_rfl hlh.le).trans (key hi hlh.le le_rfl).symm)
            have hDL : ¬ D ≤ L := by
              intro hDL
              have hconst : ∀ y ∈ affSpace z₀ W, y ∈ integralPoints n → inner ℝ a y = (inner ℝ a z₀ : ℝ) := by
                intro y hy hyZ
                have h := (haL _ hy).mp (hDL (hΛD _ (hdiff y hy hyZ)))
                exact sub_eq_zero.mp ((hsubi _ a y z₀).symm.trans h)
              rcases le_or_gt (inner ℝ a v : ℝ) (inner ℝ a z₀) with h | h
              · exact hslab (inner ℝ a v - 1) (inner ℝ a z₀) ((sub_one_lt _).trans_le h) (sub_one_lt _).le h
                  fun y hy hyZ hh => hh.2.ne (hconst y hy hyZ)
              · exact hslab (inner ℝ a z₀) (inner ℝ a v) h h.le le_rfl
                  fun y hy hyZ hh => hh.1.ne' (hconst y hy hyZ)
            have hDW : D ≤ W := hD ▸ Submodule.span_le.mpr Set.inter_subset_left
            refine ⟨?_, fun hrat => ?_⟩
            · exact hrank _ L D W hLW hDW hDL hfr
            have hex : ∃ l₁ ∈ Λ, inner ℝ a l₁ ≠ (0:ℝ) := by
              by_contra hcon
              apply hDL
              rw [hD, Submodule.span_le]
              intro l hl
              exact (haL l hl.1).mpr (by_contra fun h => hcon ⟨l, (hΛ l).mpr hl, h⟩)
            obtain ⟨l₁, hl₁, hl₁0⟩ := hex
            rcases c_dense _ Λ a with hdense | ⟨l₀, hl₀, hk⟩
            · exact hdisc _ Λ (integralPoints n) (L ⊓ D) a l₁ hl₁ hl₁0 (fun l hl => ((hΛ l).mp hl).2)
                (fun l hl t h => ⟨(haL _ (W.sub_mem ((hΛ l).mp hl).1 (W.smul_mem _ ((hΛ l₁).mp hl₁).1))).mpr h,
                  D.sub_mem (hΛD l hl) (D.smul_mem _ (hΛD l₁ hl₁))⟩)
                (fun m hm => (haL m (hLW hm.1)).mp hm.1) (fun m hm hmI => (hΛ m).mpr ⟨hLW hm.1, hmI⟩) hfinI hrat hdense
            · have hg0 : inner ℝ a l₀ ≠ (0:ℝ) := by
                intro h
                obtain ⟨k, hk⟩ := hk l₁ hl₁
                exact hl₁0 (hk.trans ((congrArg (fun r => (k:ℝ) * r) h).trans (mul_zero _)))
              obtain ⟨lo, hi, h1, h2, h3, h4⟩ := hgap _ (inner ℝ a z₀) (inner ℝ a v) hg0
              refine hslab lo hi h1 h2 h3 fun y hy hyZ => ?_
              obtain ⟨m, hm⟩ := hk _ (hdiff y hy hyZ)
              exact h4 m _ ((hsubi _ a y z₀).symm.trans hm)
          have Qcompact : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (S : Set (EuclideanSpace ℝ (Fin n))) (p : EuclideanSpace ℝ (Fin n)),
              p ∈ intRel (affSpace z₀ W) S → S ⊆ affSpace z₀ W →
              IsCompact {a : EuclideanSpace ℝ (Fin n) | a ∈ W ∧ ∀ x ∈ S, inner ℝ a (x - p) ≤ 1} := by
            clear * - n
            have gen : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
                (W : Submodule ℝ E) (S : Set E) (p : E) (ε : ℝ), 0 < ε →
                (∀ a ∈ W, ‖a‖ < ε → p + a ∈ S) → IsCompact {a : E | a ∈ W ∧ ∀ x ∈ S, inner ℝ a (x - p) ≤ 1} := by
              intro E _ _ _ W S p ε hε hS
              have : ProperSpace E := FiniteDimensional.proper ℝ E
              refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
              · have h2 : IsClosed (⋂ x ∈ S, {a : E | inner ℝ a (x - p) ≤ 1}) :=
                  isClosed_biInter fun x _ => isClosed_le (continuous_id.inner continuous_const) continuous_const
                have e : {a : E | a ∈ W ∧ ∀ x ∈ S, inner ℝ a (x - p) ≤ 1} =
                    (W : Set E) ∩ ⋂ x ∈ S, {a : E | inner ℝ a (x - p) ≤ 1} :=
                  Set.ext fun a => and_congr Iff.rfl (by rw [Set.mem_iInter₂]; exact Iff.rfl)
                rw [e]
                exact W.closed_of_finiteDimensional.inter h2
              · refine (Metric.isBounded_iff_subset_closedBall (0 : E)).2 ⟨2 / ε, ?_⟩
                rintro a ⟨haW, ha⟩
                rw [mem_closedBall_zero_iff]
                rcases eq_or_ne a 0 with rfl | ha0
                · rw [norm_zero]; exact (div_pos two_pos hε).le
                have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha0
                have hm := ha _ (hS ((ε / 2 / ‖a‖) • a) (W.smul_mem _ haW) (by
                  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (half_pos hε) hn), div_mul_cancel₀ _ hn.ne']
                  exact half_lt_self hε))
                rw [add_sub_cancel_left, inner_smul_right, real_inner_self_eq_norm_mul_norm, ← mul_assoc,
                  div_mul_cancel₀ _ hn.ne'] at hm
                rw [le_div_iff₀ hε]
                linarith only [hm]
            intro z₀ W S p hp hSA
            obtain ⟨hpS, ε, hε, hball⟩ := hp
            refine gen _ W S p ε hε fun a ha hn => hball ⟨?_, ?_⟩
            · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hn
            · show p + a - z₀ ∈ W
              rw [add_sub_right_comm]; exact W.add_mem (hSA hpS) ha
          have finstep : ∀ (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (S : Set (EuclideanSpace ℝ (Fin n))) (p : EuclideanSpace ℝ (Fin n))
              (Y : Finset (EuclideanSpace ℝ (Fin n))),
              IsCompact {a : EuclideanSpace ℝ (Fin n) | a ∈ W ∧ ∀ x ∈ S, inner ℝ a (x - p) ≤ 1} →
              (∀ y ∈ Y, ∃ a ∈ W, (∀ x ∈ S, inner ℝ a (x - p) ≤ 1) ∧ 1 ≤ inner ℝ a (y - p)) →
              (∀ y ∈ Y, ∀ y' ∈ Y, (∀ i, ((⌊y i⌋ : ℤ) : ZMod 2) = ((⌊y' i⌋ : ℤ) : ZMod 2)) →
                (1/2 : ℝ) • (y + y') ∈ Y) →
              ∃ g : (Fin n → ZMod 2) → EuclideanSpace ℝ (Fin n),
                (∀ π, g π ∈ W ∧ ∀ x ∈ S, inner ℝ (g π) (x - p) ≤ 1) ∧
                ∀ y ∈ Y, ∃ π, 1 ≤ inner ℝ (g π) (y - p) := by
            clear * - n
            classical
            have gen : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ι : Type) (par : E → ι)
                (Q : Set E) (p : E) (Y : Finset E), IsCompact Q → (0 : E) ∈ Q →
                (∀ a ∈ Q, ∀ c : ℝ, 0 ≤ c → c < 1 → c • a ∈ Q) →
                (∀ y ∈ Y, ∃ a ∈ Q, 1 ≤ inner ℝ a (y - p)) →
                (∀ y ∈ Y, ∀ y' ∈ Y, par y = par y' → (1/2 : ℝ) • (y + y') ∈ Y) →
                ∃ g : ι → E, (∀ π, g π ∈ Q) ∧ ∀ y ∈ Y, ∃ π, 1 ≤ inner ℝ (g π) (y - p) := by
              intro E _ _ ι par Q p Y hQc hQ0 hQs hsep hmid
              set C : Set (Y → E) :=
                {f | (∀ y, f y ∈ Q) ∧ ∀ t : Y, ∃ y : Y, 1 ≤ inner ℝ (f y) ((t : E) - p)} with hC
              have hCc : IsCompact C := by
                have h1 : IsCompact (Set.pi Set.univ (fun _ : Y => Q)) := isCompact_univ_pi fun _ => hQc
                have h2 : IsClosed (⋂ t : Y, ⋃ y : Y, {f : Y → E |
                    1 ≤ inner ℝ (f y) ((t : E) - p)}) := by
                  refine isClosed_iInter fun t => isClosed_iUnion_of_finite fun y => ?_
                  exact isClosed_le continuous_const ((continuous_apply y).inner continuous_const)
                have e : C = Set.pi Set.univ (fun _ : Y => Q) ∩ ⋂ t : Y, ⋃ y : Y, {f : Y → E |
                    1 ≤ inner ℝ (f y) ((t : E) - p)} := by
                  refine Set.ext fun f => and_congr ⟨fun h y _ => h y, fun h y => h y (Set.mem_univ _)⟩ ?_
                  rw [Set.mem_iInter]
                  refine forall_congr' fun t => ?_
                  rw [Set.mem_iUnion]
                  exact Iff.rfl
                rw [e]
                exact h1.inter_right h2
              have hCne : C.Nonempty := by
                choose a ha using hsep
                refine ⟨fun y => a y.1 y.2, fun y => (ha y.1 y.2).1,
                  fun t => ⟨t, (ha t.1 t.2).2⟩⟩
              obtain ⟨f, hfC, hfmin⟩ := hCc.exists_isMinOn hCne
                (f := fun f : Y → E => ∑ y, ‖f y‖) (by fun_prop)
              have htight : ∀ y : Y, ∃ t : Y, f y ≠ 0 → inner ℝ (f y) ((t : E) - p) = 1 ∧
                  ∀ y', y' ≠ y → inner ℝ (f y') ((t : E) - p) < 1 := by
                intro y
                by_contra hcon
                push Not at hcon
                have hfy : f y ≠ 0 := (hcon y).1
                have hcon' : ∀ t : Y, inner ℝ (f y) ((t : E) - p) = 1 →
                  ∃ y', y' ≠ y ∧ 1 ≤ inner ℝ (f y') ((t : E) - p) := fun t => (hcon t).2
                have hc : ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ t : Y,
                    (∀ y', y' ≠ y → inner ℝ (f y') ((t : E) - p) < 1) →
                    1 ≤ c * inner ℝ (f y) ((t : E) - p) := by
                  set Z : Finset Y := Finset.univ.filter
                    (fun t => ∀ y', y' ≠ y → inner ℝ (f y') ((t : E) - p) < 1) with hZ
                  rcases Z.eq_empty_or_nonempty with h | h
                  · refine ⟨0, le_rfl, one_pos, fun t ht => ?_⟩
                    have : t ∈ Z := by simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and]; exact ht
                    rw [h] at this; simp at this
                  · obtain ⟨t₀, ht₀, hmin⟩ := Z.exists_min_image
                      (fun t => inner ℝ (f y) ((t : E) - p)) h
                    have ht₀' : ∀ y', y' ≠ y → inner ℝ (f y') ((t₀ : E) - p) < 1 := by
                      simpa only [hZ, Finset.mem_filter, Finset.mem_univ, true_and] using ht₀
                    have hm1 : 1 ≤ inner ℝ (f y) ((t₀ : E) - p) := by
                      obtain ⟨y', hy'⟩ := hfC.2 t₀
                      by_cases e : y' = y
                      · rwa [e] at hy'
                      · exact absurd (ht₀' y' e) (not_lt.mpr hy')
                    have hm2 : inner ℝ (f y) ((t₀ : E) - p) ≠ 1 := by
                      intro e
                      obtain ⟨y', hy', h'⟩ := hcon' t₀ e
                      exact absurd (ht₀' y' hy') (not_lt.mpr h')
                    have hm3 := lt_of_le_of_ne hm1 (Ne.symm hm2)
                    refine ⟨(inner ℝ (f y) ((t₀ : E) - p))⁻¹, by positivity,
                      inv_lt_one_of_one_lt₀ hm3, fun t ht => ?_⟩
                    have htZ : t ∈ Z := by simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and]; exact ht
                    have := hmin t htZ
                    rw [inv_mul_eq_div, le_div_iff₀ (by linarith), one_mul]
                    exact this
                obtain ⟨c, hc0, hc1, hc⟩ := hc
                have hup : Function.update f y (c • f y) ∈ C := by
                  refine ⟨fun y' => ?_, fun t => ?_⟩
                  · by_cases e : y' = y
                    · subst e; rw [Function.update_self]; exact hQs _ (hfC.1 _) c hc0 hc1
                    · rw [Function.update_of_ne e]; exact hfC.1 _
                  · by_cases h : ∀ y', y' ≠ y → inner ℝ (f y') ((t : E) - p) < 1
                    · refine ⟨y, ?_⟩
                      rw [Function.update_self, real_inner_smul_left]; exact hc t h
                    · push Not at h
                      obtain ⟨y', e, h⟩ := h
                      exact ⟨y', by rwa [Function.update_of_ne e]⟩
                have hle := hfmin hup
                have hself : ‖Function.update f y (c • f y) y‖ = c * ‖f y‖ := by
                  rw [Function.update_self, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
                have hlt : ∑ y', ‖Function.update f y (c • f y) y'‖ < ∑ y', ‖f y'‖ := by
                  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨y, Finset.mem_univ _, ?_⟩
                  · by_cases e : i = y
                    · rw [e, hself]
                      exact mul_le_of_le_one_left (norm_nonneg _) hc1.le
                    · rw [Function.update_of_ne e]
                  · rw [hself]
                    exact mul_lt_of_lt_one_left (norm_pos_iff.mpr hfy) hc1
                exact absurd hlt (not_lt.mpr hle)
              choose tt htt using htight
              have hinj : ∀ y y' : Y, f y ≠ 0 → f y' ≠ 0 →
                  par (tt y : E) =
                    par (tt y' : E) → y = y' := by
                intro y y' hy hy' hpar
                by_contra hne
                have hm := hmid _ (tt y).2 _ (tt y').2 hpar
                obtain ⟨c, hc⟩ := hfC.2 ⟨_, hm⟩
                have e : inner ℝ (f c) ((1/2 : ℝ) • ((tt y : E) + tt y') - p) =
                    (inner ℝ (f c) ((tt y : E) - p) + inner ℝ (f c) ((tt y' : E) - p)) / 2 := by
                  simp only [inner_sub_right, inner_smul_right, inner_add_right]
                  ring
                have hc' : 1 ≤ inner ℝ (f c) ((1/2 : ℝ) • ((tt y : E) + tt y') - p) := hc
                rw [e] at hc'
                obtain ⟨h1, h2⟩ := htt y hy
                obtain ⟨h1', h2'⟩ := htt y' hy'
                have key : ∀ u v : ℝ, 1 ≤ (u + v) / 2 → (u = 1 ∨ u < 1) → v < 1 → False := fun u v h hu hv => by
                  rcases hu with hu | hu <;> linarith only [h, hu, hv]
                by_cases ec : c = y
                · refine key _ _ hc' (Or.inl (by rw [ec]; exact h1)) (h2' c (by rw [ec]; exact hne))
                · refine key _ _ (by rw [add_comm]; exact hc') ?_ (h2 c ec)
                  by_cases ec' : c = y'
                  · exact Or.inl (by rw [ec']; exact h1')
                  · exact Or.inr (h2' c ec')
              refine ⟨fun π => if h : ∃ y : Y, f y ≠ 0 ∧
                par (tt y : E) = π then f h.choose else 0, ?_, ?_⟩
              · intro π
                beta_reduce
                split_ifs with h
                · exact hfC.1 _
                · exact hQ0
              · intro t ht
                obtain ⟨y, hy⟩ := hfC.2 ⟨t, ht⟩
                have hfy : f y ≠ 0 := by
                  intro e
                  rw [e, inner_zero_left] at hy
                  linarith
                have hex : ∃ y' : Y, f y' ≠ 0 ∧ par (tt y' : E) =
                  par (tt y : E) := ⟨y, hfy, rfl⟩
                refine ⟨par (tt y : E), ?_⟩
                beta_reduce
                rw [dif_pos hex]
                have := hinj _ _ hex.choose_spec.1 hfy hex.choose_spec.2
                rw [this]
                exact hy
            intro W S p Y hQc hsep hmid
            refine gen _ (Fin n → ZMod 2) (fun y i => ((⌊y i⌋ : ℤ) : ZMod 2)) _ p Y hQc
              ⟨W.zero_mem, fun x _ => by rw [inner_zero_left]; exact zero_le_one⟩ ?_ ?_ ?_
            · rintro a ⟨ha, ha'⟩ c h0 h1
              refine ⟨W.smul_mem _ ha, fun x hx => ?_⟩
              rw [real_inner_smul_left]
              exact (mul_le_mul_of_nonneg_left (ha' x hx) h0).trans (by rw [mul_one]; exact h1.le)
            · intro y hy
              obtain ⟨a, h1, h2, h3⟩ := hsep y hy
              exact ⟨a, ⟨h1, h2⟩, h3⟩
            · intro y hy y' hy' h
              exact hmid y hy y' hy' (fun i => congrFun h i)
          have lovasz : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (S : Set (EuclideanSpace ℝ (Fin n))) (p : EuclideanSpace ℝ (Fin n)),
              IsMaximalLatticeFree z₀ W S → p ∈ intRel (affSpace z₀ W) S →
              ∃ T : Finset (EuclideanSpace ℝ (Fin n) × ℝ),
                S = affSpace z₀ W ∩ {x | ∀ c ∈ T, inner ℝ c.1 x ≤ c.2} := by
            clear * - strict_of_intRel affconv polyconv sep_point Qcompact finstep n
            classical
            intro z₀ W S p hmax hp
            obtain ⟨⟨hSA, hconv, hlf⟩, hmaxS⟩ := hmax
            have hQc := Qcompact z₀ W S p hp hSA
            have hfin : ∀ N : ℕ, {x : EuclideanSpace ℝ (Fin n) | x ∈ affSpace z₀ W ∧ x ∈ integralPoints n ∧ ‖x‖ ≤ N}.Finite := by
              intro N
              have h1 : (Set.pi Set.univ (fun _ : Fin n => Set.Icc (-(N:ℤ)) N)).Finite :=
                Set.Finite.pi (fun _ => Set.finite_Icc _ _)
              refine (h1.image (fun z : Fin n → ℤ => (WithLp.toLp 2 (fun i => (z i : ℝ)) : EuclideanSpace ℝ (Fin n)))).subset ?_
              rintro x ⟨-, hx, hN⟩
              choose w hw using hx
              refine ⟨w, ?_, ?_⟩
              · intro i _
                have h2 : ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
                rw [Real.norm_eq_abs, hw i] at h2
                have h3 := abs_le.1 (h2.trans hN)
                constructor
                · exact_mod_cast h3.1
                · exact_mod_cast h3.2
              · ext i
                exact (hw i).symm
            have hg : ∀ N : ℕ, ∃ g : (Fin n → ZMod 2) → EuclideanSpace ℝ (Fin n),
                (∀ π, g π ∈ W ∧ ∀ x ∈ S, inner ℝ (g π) (x - p) ≤ 1) ∧
                ∀ y ∈ affSpace z₀ W, y ∈ integralPoints n → ‖y‖ ≤ N → ∃ π, 1 ≤ inner ℝ (g π) (y - p) := by
              intro N
              obtain ⟨g, hg1, hg2⟩ := finstep W S p (hfin N).toFinset hQc (by
                intro y hy
                rw [Set.Finite.mem_toFinset] at hy
                exact sep_point z₀ W S p y hSA hconv hp hy.1 (fun h => hlf y h hy.2.1)) (by
                intro y hy y' hy' hpar
                rw [Set.Finite.mem_toFinset] at hy hy' ⊢
                obtain ⟨h1, h2, h3⟩ := hy
                obtain ⟨h1', h2', h3'⟩ := hy'
                refine ⟨?_, ?_, ?_⟩
                · rw [smul_add]
                  exact affconv z₀ W h1 h1' one_half_pos.le one_half_pos.le (add_halves 1)
                · intro i
                  obtain ⟨k, hk⟩ := h2 i
                  obtain ⟨k', hk'⟩ := h2' i
                  have := hpar i
                  rw [hk, hk', Int.floor_intCast, Int.floor_intCast, ZMod.intCast_eq_intCast_iff,
                    Int.modEq_iff_dvd] at this
                  obtain ⟨m, hm⟩ := this
                  refine ⟨k + m, ?_⟩
                  have hm' : (k' : ℝ) - k = 2 * m := by exact_mod_cast hm
                  show (1/2 : ℝ) * (y.ofLp i + y'.ofLp i) = _
                  rw [hk, hk']
                  push_cast
                  linarith
                · rw [norm_smul]
                  have := norm_add_le y y'
                  norm_num
                  linarith)
              refine ⟨g, hg1, fun y h1 h2 h3 => hg2 y ?_⟩
              rw [Set.Finite.mem_toFinset]
              exact ⟨h1, h2, h3⟩
            choose g hg1 hg2 using hg
            have hcpt : IsCompact (Set.pi Set.univ (fun _ : (Fin n → ZMod 2) =>
              {a : EuclideanSpace ℝ (Fin n) | a ∈ W ∧ ∀ x ∈ S, inner ℝ a (x - p) ≤ 1})) :=
              isCompact_univ_pi fun _ => hQc
            obtain ⟨a, ha, φ, hφ, hlim⟩ := hcpt.tendsto_subseq (x := g) (fun N π _ => hg1 N π)
            have ha' : ∀ π, a π ∈ W ∧ ∀ x ∈ S, inner ℝ (a π) (x - p) ≤ 1 := fun π => ha π (Set.mem_univ _)
            set T : Finset (EuclideanSpace ℝ (Fin n) × ℝ) :=
              Finset.univ.image (fun π => (a π, 1 + inner ℝ (a π) p)) with hT
            have hTmem : ∀ x, (∀ c ∈ T, inner ℝ c.1 x ≤ c.2) ↔ ∀ π, inner ℝ (a π) (x - p) ≤ 1 := by
              intro x
              rw [hT]
              simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
                forall_apply_eq_imp_iff, inner_sub_right]
              exact forall_congr' fun π => by constructor <;> intro h <;> linarith
            refine ⟨T, (hmaxS _ ⟨Set.inter_subset_left, ?_, ?_⟩ ?_).symm⟩
            · exact (affconv z₀ W).inter (polyconv T)
            · intro y hy hyI
              have hyA : y ∈ affSpace z₀ W := hy.1.1
              have hstrict : ∀ π, inner ℝ (a π) (y - p) < 1 := by
                intro π
                have := strict_of_intRel z₀ W _ (a π) p y (1 + inner ℝ (a π) p) Set.inter_subset_left
                  (fun x hx => by
                    have := (hTmem x).1 hx.2 π
                    rw [inner_sub_right] at this
                    linarith) (hSA hp.1) (by linarith) hy
                rw [inner_sub_right]
                linarith
              have hev : ∀ π, ∀ᶠ N in Filter.atTop, inner ℝ (g (φ N) π) (y - p) < 1 := by
                intro π
                have h1 : Filter.Tendsto (fun N => g (φ N) π) Filter.atTop (nhds (a π)) :=
                  (tendsto_pi_nhds.1 hlim) π
                have h2 : Filter.Tendsto (fun N => inner ℝ (g (φ N) π) (y - p)) Filter.atTop
                  (nhds (inner ℝ (a π) (y - p))) := h1.inner tendsto_const_nhds
                exact h2.eventually_lt_const (hstrict π)
              obtain ⟨M, hM⟩ := exists_nat_ge ‖y‖
              obtain ⟨N, hN1, hN2⟩ := ((Filter.eventually_all.2 hev).and (Filter.eventually_ge_atTop M)).exists
              obtain ⟨π, hπ⟩ := hg2 (φ N) y hyA hyI (hM.trans (by exact_mod_cast hN2.trans (hφ.id_le N)))
              exact absurd (hN1 π) (not_lt.mpr hπ)
            · intro x hx
              exact ⟨hSA hx, (hTmem x).2 fun π => (ha' π).2 x hx⟩
          have case_a_fwd : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W D : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (S : Set (EuclideanSpace ℝ (Fin n))) (p : EuclideanSpace ℝ (Fin n)), D ≤ W →
              (∀ x ∈ affSpace z₀ W, x ∈ integralPoints n → x ∈ affSpace z₀ D) →
              p ∈ intRel (affSpace z₀ W) S → p ∈ affSpace z₀ D → IsMaximalLatticeFree z₀ W S →
              (IsPolyhedronIn ⊤ S ∧ S ⊆ affSpace z₀ W ∧ affDim S = (Module.finrank ℝ W : ℤ) ∧
                  IsMaximalLatticeFree z₀ D (S ∩ affSpace z₀ D) ∧
                  affDim (S ∩ affSpace z₀ D) = (Module.finrank ℝ D : ℤ) ∧
                  (∀ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F →
                    IsFacet (S ∩ affSpace z₀ D) (F ∩ affSpace z₀ D)) ∧
                  (∀ F G : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F → IsFacet S G →
                    F ∩ affSpace z₀ D = G ∩ affSpace z₀ D → F = G) ∧
                  (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                    IsFacet (S ∩ affSpace z₀ D) G →
                    ∃ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F ∧
                      F ∩ affSpace z₀ D = G)) := by
            clear * - fulldim irred facets aff_poly affconv polyconv lf_of_trace trace_lf lovasz n
            intro z₀ W D S p hDW hint hp hpD hmax
            have hDA : affSpace z₀ D ⊆ affSpace z₀ W := fun x hx => hDW hx
            have hSA := hmax.1.1
            have hB := trace_lf z₀ W D S p hDW hp hpD hmax.1
            have hBmax : IsMaximalLatticeFree z₀ D (S ∩ affSpace z₀ D) := by
              refine ⟨hB, fun B' hB' hsub => ?_⟩
              have hne : B'.Nonempty := ⟨p, hsub ⟨hp.1, hpD⟩⟩
              have hcv : IsLatticeFree z₀ W (convexHull ℝ (S ∪ B')) := by
                refine lf_of_trace z₀ W D _ B' hDW hint ?_ (convex_convexHull ℝ _) ?_ hB'
                · exact convexHull_min (Set.union_subset hSA (hB'.1.trans hDA)) (affconv z₀ W)
                · apply Set.Subset.antisymm
                  · rintro x ⟨hx, hxD⟩
                    rw [hmax.1.2.1.convexHull_union hB'.2.1 ⟨p, hp.1⟩ hne, mem_convexJoin] at hx
                    obtain ⟨s, hs, b, hb, hx⟩ := hx
                    obtain ⟨u, v, hu, hv, huv, rfl⟩ := hx
                    rcases eq_or_ne u 0 with rfl | hu0
                    · obtain rfl : v = 1 := by linarith
                      simpa using hb
                    · have hsD : s ∈ affSpace z₀ D := by
                        have h1 : u • s + v • b - z₀ ∈ D := hxD
                        have h2 : b - z₀ ∈ D := hB'.1 hb
                        show s - z₀ ∈ D
                        have : s - z₀ = u⁻¹ • ((u • s + v • b - z₀) - v • (b - z₀)) := by
                          obtain rfl : v = 1 - u := by linarith
                          match_scalars <;> field_simp <;> ring
                        rw [this]
                        exact D.smul_mem _ (D.sub_mem h1 (D.smul_mem _ h2))
                      exact hB'.2.1 (hsub ⟨hs, hsD⟩) hb hu hv huv
                  · intro x hx
                    exact ⟨subset_convexHull ℝ _ (Or.inr hx), hB'.1 hx⟩
              have := hmax.2 _ hcv (Set.subset_union_left.trans (subset_convexHull ℝ _))
              refine Set.Subset.antisymm (fun x hx => ⟨?_, hB'.1 hx⟩) hsub
              rw [← this]
              exact subset_convexHull ℝ _ (Or.inr hx)
            obtain ⟨T, hT⟩ := lovasz z₀ W S p hmax hp
            have hBrep : S ∩ affSpace z₀ D = affSpace z₀ D ∩ {x | ∀ c ∈ T, inner ℝ c.1 x ≤ c.2} := by
              conv_lhs => rw [hT]
              ext x
              constructor
              · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3, h2⟩
              · rintro ⟨h1, h2⟩; exact ⟨⟨hDA h1, h2⟩, h1⟩
            have hpB : p ∈ intRel (affSpace z₀ D) (S ∩ affSpace z₀ D) := by
              obtain ⟨hpS, ε, hε, hball⟩ := hp
              exact ⟨⟨hpS, hpD⟩, ε, hε, fun y hy => ⟨hball ⟨hy.1, hDA hy.2⟩, hy.2⟩⟩
            obtain ⟨T', hT'T, hT', hp', hq'⟩ := irred z₀ D T _ hBrep
              (fulldim z₀ D _ p Set.inter_subset_right hpB)
            have hS' : S = affSpace z₀ W ∩ {x | ∀ c ∈ T', inner ℝ c.1 x ≤ c.2} := by
              symm
              apply hmax.2
              · refine lf_of_trace z₀ W D _ _ hDW hint Set.inter_subset_left
                  ((affconv z₀ W).inter (polyconv T')) ?_ hB
                rw [hT']
                ext x
                constructor
                · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3, h2⟩
                · rintro ⟨h1, h2⟩; exact ⟨⟨hDA h1, h2⟩, h1⟩
              · rw [hT]
                rintro x ⟨h1, h2⟩
                exact ⟨h1, fun c hc => h2 c (hT'T hc)⟩
            have hfS := facets z₀ W T' S hS' (by obtain ⟨p', h1, h2⟩ := hp'; exact ⟨p', hDA h1, h2⟩)
              (fun c hc => by obtain ⟨q, h1, h2⟩ := hq' c hc; exact ⟨q, hDA h1, h2⟩)
            have hfB := facets z₀ D T' _ hT' hp' hq'
            refine ⟨?_, hSA, hfS.1, hBmax, hfB.1, ?_, ?_, ?_⟩
            · rw [hT]; exact aff_poly z₀ W T
            · intro F hF
              obtain ⟨c, hc, rfl⟩ := hfS.2.2 F hF
              rw [Set.inter_right_comm]
              exact hfB.2.1 c hc
            · intro F G hF hG hFG
              obtain ⟨c, hc, rfl⟩ := hfS.2.2 F hF
              obtain ⟨d, hd, rfl⟩ := hfS.2.2 G hG
              by_cases hcd : c = d
              · rw [hcd]
              obtain ⟨q, hq1, hq2, hq3⟩ := hq' c hc
              have hqS : q ∈ S := by
                rw [hS']
                refine ⟨hDA hq1, fun e he => ?_⟩
                by_cases hec : e = c
                · rw [hec, hq2]
                · exact (hq3 e he hec).le
              have : q ∈ (S ∩ {x | inner ℝ c.1 x = c.2}) ∩ affSpace z₀ D := ⟨⟨hqS, hq2⟩, hq1⟩
              rw [hFG] at this
              exact absurd this.1.2 (hq3 d hd (Ne.symm hcd)).ne
            · intro G hG
              obtain ⟨c, hc, rfl⟩ := hfB.2.2 G hG
              exact ⟨_, hfS.2.1 c hc, Set.inter_right_comm _ _ _⟩
          have case_a_rev : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W D : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (S : Set (EuclideanSpace ℝ (Fin n))), D ≤ W →
              (∀ x ∈ affSpace z₀ W, x ∈ integralPoints n → x ∈ affSpace z₀ D) →
              IsPolyhedronIn ⊤ S → S ⊆ affSpace z₀ W → affDim S = (Module.finrank ℝ W : ℤ) →
              IsMaximalLatticeFree z₀ D (S ∩ affSpace z₀ D) →
              affDim (S ∩ affSpace z₀ D) = (Module.finrank ℝ D : ℤ) →
              (∀ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F →
                    IsFacet (S ∩ affSpace z₀ D) (F ∩ affSpace z₀ D)) →
              (∀ F G : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F → IsFacet S G →
                    F ∩ affSpace z₀ D = G ∩ affSpace z₀ D → F = G) →
              IsMaximalLatticeFree z₀ W S := by
            clear * - facet_nested irred facets intRel_of_strict poly_finset affconv polyconv lf_of_trace trace_lf n
            classical
            intro z₀ W D S hDW hint hpoly hSA hdim hBmax hBdim hfac hinj
            have hDA : affSpace z₀ D ⊆ affSpace z₀ W := fun x hx => hDW hx
            obtain ⟨T₀, hT₀⟩ := poly_finset S hpoly
            have hT₀' : S = affSpace z₀ W ∩ {x | ∀ c ∈ T₀, inner ℝ c.1 x ≤ c.2} := by
              rw [← hT₀]; exact (Set.inter_eq_right.2 hSA).symm
            obtain ⟨T, -, hT, hp, hq⟩ := irred z₀ W T₀ S hT₀' hdim
            obtain ⟨-, hf1, -⟩ := facets z₀ W T S hT hp hq
            have hSconv : Convex ℝ S := by rw [hT]; exact (affconv z₀ W).inter (polyconv T)
            set B := S ∩ affSpace z₀ D with hBdef
            have hBconv : Convex ℝ B := hSconv.inter (affconv z₀ D)
            have hBne : B.Nonempty := by
              by_contra h
              unfold affDim at hBdim
              rw [if_neg h] at hBdim
              omega
            have havgR : ∀ x y b : ℝ, x ≤ b → y ≤ b → (x < b ∨ y < b) → 1/2 * x + 1/2 * y < b := by
              intro x y b h1 h2 h3
              rcases h3 with h3 | h3 <;> linarith only [h1, h2, h3]
            have havg : ∀ (K : Set (EuclideanSpace ℝ (Fin n))) (T' : Finset (EuclideanSpace ℝ (Fin n) × ℝ)),
                Convex ℝ K → K.Nonempty → (∀ c ∈ T', ∀ x ∈ K, inner ℝ c.1 x ≤ c.2) →
                (∀ c ∈ T', ∃ x ∈ K, inner ℝ c.1 x < c.2) → ∃ x ∈ K, ∀ c ∈ T', inner ℝ c.1 x < c.2 := by
              intro K T' hK hKne
              refine Finset.induction_on T' (fun _ _ => ?_) (fun c T' hc ih hval hst => ?_)
              · obtain ⟨x, hx⟩ := hKne; exact ⟨x, hx, fun c hc => absurd hc (Finset.notMem_empty c)⟩
              · obtain ⟨x, hx, hx'⟩ := ih (fun d hd => hval d (Finset.mem_insert_of_mem hd))
                  (fun d hd => hst d (Finset.mem_insert_of_mem hd))
                obtain ⟨y, hy, hy'⟩ := hst c (Finset.mem_insert_self _ _)
                refine ⟨(1/2 : ℝ) • x + (1/2 : ℝ) • y, hK hx hy one_half_pos.le one_half_pos.le (add_halves 1), ?_⟩
                intro d hd
                rw [inner_add_right, inner_smul_right, inner_smul_right]
                refine havgR _ _ _ (hval d hd x hx) (hval d hd y hy) ?_
                rcases Finset.mem_insert.1 hd with rfl | hd'
                · exact Or.inr hy'
                · exact Or.inl (hx' d hd')
            have hvalS : ∀ c ∈ T, ∀ x ∈ S, inner ℝ c.1 x ≤ c.2 := by
              intro c hc x hx
              rw [hT] at hx
              exact hx.2 c hc
            have hBS : ∀ x ∈ B, x ∈ S := fun x hx => hx.1
            -- common strict point of B
            obtain ⟨p, hpB, hpT⟩ : ∃ x ∈ B, ∀ c ∈ T, inner ℝ c.1 x < c.2 := by
              refine havg B T hBconv hBne (fun c hc x hx => hvalS c hc x hx.1) ?_
              intro c hc
              by_contra hcon
              push Not at hcon
              have heq : (S ∩ {x | inner ℝ c.1 x = c.2}) ∩ affSpace z₀ D = B := by
                ext x
                constructor
                · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h3⟩
                · intro hx
                  exact ⟨⟨hx.1, le_antisymm (hvalS c hc x hx.1) (hcon x hx)⟩, hx.2⟩
              have := (hfac _ (hf1 c hc)).2.1
              rw [heq] at this
              omega
            have hpint : p ∈ intRel (affSpace z₀ W) S := by
              rw [hT]; exact intRel_of_strict z₀ W T p (hSA hpB.1) hpT
            -- relative interior points of the facets F_c ∩ V
            have hqB : ∀ c ∈ T, ∃ q ∈ B, inner ℝ c.1 q = c.2 ∧ ∀ d ∈ T, d ≠ c → inner ℝ d.1 q < d.2 := by
              intro c hc
              have hFc := hfac _ (hf1 c hc)
              obtain ⟨q, hqK, hqT⟩ := havg ((S ∩ {x | inner ℝ c.1 x = c.2}) ∩ affSpace z₀ D) (T.erase c)
                (by
                  refine Convex.inter (Convex.inter hSconv ?_) (affconv z₀ D)
                  intro x hx y hy s t hs ht hst
                  show inner ℝ c.1 _ = c.2
                  rw [inner_add_right, inner_smul_right, inner_smul_right, show inner ℝ c.1 x = c.2 from hx,
                    show inner ℝ c.1 y = c.2 from hy, ← add_mul, hst, one_mul])
                hFc.1 (fun d hd x hx => hvalS d (Finset.mem_of_mem_erase hd) x hx.1.1) (by
                  intro d hd
                  have hdT := Finset.mem_of_mem_erase hd
                  have hdc := Finset.ne_of_mem_erase hd
                  by_contra hcon
                  push Not at hcon
                  have hsub : (S ∩ {x | inner ℝ c.1 x = c.2}) ∩ affSpace z₀ D ⊆
                      (S ∩ {x | inner ℝ d.1 x = d.2}) ∩ affSpace z₀ D := fun x hx =>
                    ⟨⟨hx.1.1, le_antisymm (hvalS d hdT x hx.1.1) (hcon x hx)⟩, hx.2⟩
                  have h1 := facet_nested _ _ _ hFc (hfac _ (hf1 d hdT)) hsub
                  have h2 := hinj _ _ (hf1 c hc) (hf1 d hdT) h1
                  obtain ⟨q, hq1, hq2, hq3⟩ := hq c hc
                  have hqS : q ∈ S := by
                    rw [hT]
                    refine ⟨hq1, fun e he => ?_⟩
                    by_cases hec : e = c
                    · rw [hec, hq2]
                    · exact (hq3 e he hec).le
                  have h3 : q ∈ S ∩ {x | inner ℝ c.1 x = c.2} := ⟨hqS, hq2⟩
                  rw [h2] at h3
                  exact absurd h3.2 (hq3 d hdT hdc).ne)
              exact ⟨q, ⟨hqK.1.1, hqK.2⟩, hqK.1.2, fun d hd hdc => hqT d (Finset.mem_erase.2 ⟨hdc, hd⟩)⟩
            refine ⟨lf_of_trace z₀ W D S B hDW hint hSA hSconv rfl hBmax.1, ?_⟩
            intro S' hS' hSS'
            have hp' : p ∈ intRel (affSpace z₀ W) S' := by
              obtain ⟨h1, ε, hε, h2⟩ := hpint
              exact ⟨hSS' h1, ε, hε, h2.trans hSS'⟩
            have htr : S' ∩ affSpace z₀ D = B :=
              hBmax.2 _ (trace_lf z₀ W D S' p hDW hp' hpB.2 hS') (fun x hx => ⟨hSS' hx.1, hx.2⟩)
            refine Set.Subset.antisymm ?_ hSS'
            intro x hx
            by_contra hxS
            have hxA := hS'.1 hx
            obtain ⟨c, hc, hcx⟩ : ∃ c ∈ T, c.2 < inner ℝ c.1 x := by
              by_contra hcon
              push Not at hcon
              exact hxS (by rw [hT]; exact ⟨hxA, hcon⟩)
            obtain ⟨q, hqB', hqc, hqd⟩ := hqB c hc
            -- choose small t with q - t(x - q)-ish strictly inside S, then move towards q - p
            -- s(t) = (q + t² (q-p)... ) ; use: for small t>0, y = q + (t*t)•(q-p), s = (y - t x)/(1-t) ∈ S
            have key1 : ∀ q p x b : ℝ, q = b → p < b → b < x →
                ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), q + t * t * (q - p) - t * x < (1 - t) * b := by
              intro q p x b hq hp hx
              have h1 : 0 < (x - b) / (b - p) := div_pos (sub_pos.2 hx) (sub_pos.2 hp)
              filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h1), self_mem_nhdsWithin] with t ht ht0
              have h2 : t * (b - p) < x - b := (lt_div_iff₀ (sub_pos.2 hp)).1 ht
              have h3 := mul_lt_mul_of_pos_left h2 (show (0:ℝ) < t from ht0)
              rw [hq]
              linarith only [h3]
            have key2 : ∀ q p x b : ℝ, q < b →
                ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), q + t * t * (q - p) - t * x < (1 - t) * b := by
              intro q p x b hq
              have hc1 : Continuous fun t : ℝ => q + t * t * (q - p) - t * x :=
                (continuous_const.add ((continuous_id.mul continuous_id).mul continuous_const)).sub
                  (continuous_id.mul continuous_const)
              have hc2 : Continuous fun t : ℝ => (1 - t) * b :=
                (continuous_const.sub continuous_id).mul continuous_const
              exact mem_nhdsWithin_of_mem_nhds ((isOpen_lt hc1 hc2).mem_nhds (by
                show q + 0 * 0 * (q - p) - 0 * x < (1 - 0) * b
                linarith only [hq]))
            have hev : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ d ∈ T,
                inner ℝ d.1 q + t * t * (inner ℝ d.1 q - inner ℝ d.1 p) - t * inner ℝ d.1 x < (1 - t) * d.2 := by
              rw [Filter.eventually_all_finset]
              intro d hd
              by_cases hdc : d = c
              · rw [hdc]
                exact key1 _ _ _ _ hqc (hpT c hc) hcx
              · exact key2 _ _ _ _ (hqd d hd hdc)
            have hev1 : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), t < 1 :=
              mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)
            obtain ⟨t, ht, ht1, ht0⟩ := (hev.and (hev1.and self_mem_nhdsWithin)).exists
            have ht0' : (0:ℝ) < t := ht0
            set y := q + (t * t) • (q - p) with hy
            have hyD : y ∈ affSpace z₀ D := by
              show q + (t * t) • (q - p) - z₀ ∈ D
              rw [add_sub_right_comm, ← sub_sub_sub_cancel_right q p z₀]
              exact D.add_mem hqB'.2 (D.smul_mem _ (D.sub_mem hqB'.2 hpB.2))
            have h1t : (0:ℝ) < 1 - t := by linarith
            have hsS : (1 - t)⁻¹ • (y - t • x) ∈ S := by
              rw [hT]
              refine ⟨?_, fun d hd => ?_⟩
              · show (1 - t)⁻¹ • (y - t • x) - z₀ ∈ W
                have hz : z₀ = (1 - t)⁻¹ • ((1 - t) • z₀) := (inv_smul_smul₀ h1t.ne' z₀).symm
                have e : y - t • x - (1 - t) • z₀ = (y - z₀) - t • (x - z₀) := by
                  rw [sub_smul, one_smul, smul_sub]; abel
                rw [hz, ← smul_sub, e]
                exact W.smul_mem _ (W.sub_mem (hDW hyD) (W.smul_mem _ hxA))
              · rw [inner_smul_right, inner_sub_right, inner_smul_right, inv_mul_eq_div, div_le_iff₀ h1t]
                rw [hy, inner_add_right, inner_smul_right, inner_sub_right, mul_comm d.2]
                exact (ht d hd).le
            have hyS' : y ∈ S' := by
              have := hS'.2.1 (hSS' hsS) hx h1t.le ht0'.le (by ring)
              have e : (1 - t) • ((1 - t)⁻¹ • (y - t • x)) + t • x = y := by
                rw [smul_inv_smul₀ h1t.ne']; abel
              rwa [e] at this
            have hyB : y ∈ B := by rw [← htr]; exact ⟨hyS', hyD⟩
            have h1 := hvalS c hc y hyB.1
            rw [hy, inner_add_right, inner_smul_right, inner_sub_right, hqc] at h1
            have h2 := hpT c hc
            have h3 : 0 < t * t * (c.2 - inner ℝ c.1 p) := by
              have : 0 < c.2 - inner ℝ c.1 p := by linarith
              positivity
            linarith
          have half_max : ∀ (z₀ : EuclideanSpace ℝ (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
              (a : EuclideanSpace ℝ (Fin n)) (b : ℝ), z₀ ∈ integralPoints n → (∃ w ∈ W, inner ℝ a w ≠ 0) →
              (∀ x ∈ affSpace z₀ W, x ∈ integralPoints n → inner ℝ a x = b) →
              IsMaximalLatticeFree z₀ W (affSpace z₀ W ∩ {x | inner ℝ a x ≤ b}) := by
            clear * - ir_iff half_lf n
            intro z₀ W a b hz₀I hw hVint
            have hz₀A : z₀ ∈ affSpace z₀ W := by
              show z₀ - z₀ ∈ W
              rw [sub_self]; exact W.zero_mem
            refine ⟨half_lf z₀ W a b hw hVint, ?_⟩
            intro B' hB' hSB
            refine Set.Subset.antisymm ?_ hSB
            intro p hp
            have hpA : p ∈ affSpace z₀ W := hB'.1 hp
            refine ⟨hpA, ?_⟩
            by_contra hpb
            have hpb' : b < inner ℝ a p := not_le.mp hpb
            have hz₀b : inner ℝ a z₀ = b := hVint z₀ hz₀A hz₀I
            have hδ : 0 < inner ℝ a p - b := sub_pos.2 hpb'
            have hna : 0 < 2 * ‖a‖ + 1 := by linarith only [norm_nonneg a]
            refine hB'.2.2 z₀ ((ir_iff z₀ W B' z₀ hz₀A).2 ⟨(inner ℝ a p - b) / (2 * ‖a‖ + 1), div_pos hδ hna, ?_⟩) hz₀I
            intro u hu hun
            have hq : z₀ + (z₀ - p + (2:ℝ) • u) ∈ B' := by
              refine hSB ⟨?_, ?_⟩
              · show z₀ + (z₀ - p + (2:ℝ) • u) - z₀ ∈ W
                rw [add_sub_cancel_left, ← neg_sub]
                exact W.add_mem (W.neg_mem hpA) (W.smul_mem _ hu)
              · show inner ℝ a (z₀ + (z₀ - p + (2:ℝ) • u)) ≤ b
                rw [inner_add_right, inner_add_right, inner_sub_right, inner_smul_right, hz₀b]
                have h1 : inner ℝ a u ≤ ‖a‖ * ‖u‖ := real_inner_le_norm _ _
                have h2 := (lt_div_iff₀ hna).1 hun
                have h3 := norm_nonneg u
                generalize inner ℝ a p = P at *
                generalize inner ℝ a u = U at *
                generalize ‖a‖ = A at *
                linarith only [h1, h2, h3]
            have := hB'.2.1 hp hq one_half_pos.le one_half_pos.le (add_halves 1)
            have e : (1/2 : ℝ) • p + (1/2 : ℝ) • (z₀ + (z₀ - p + (2:ℝ) • u)) = z₀ + u := by
              rw [smul_add, smul_add, smul_sub, smul_smul, one_div_mul_cancel two_ne_zero, one_smul]
              have : (1/2 : ℝ) • z₀ + (1/2 : ℝ) • z₀ = z₀ := by rw [← add_smul, add_halves, one_smul]
              rw [show (1/2 : ℝ) • p + ((1/2 : ℝ) • z₀ + ((1/2 : ℝ) • z₀ - (1/2 : ℝ) • p + u)) =
                ((1/2 : ℝ) • z₀ + (1/2 : ℝ) • z₀) + u by abel, this]
            rwa [e] at this
          have base : ∀ (z z₀ : EuclideanSpace ℝ (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))),
              z₀ ∈ affSpace z W ∩ integralPoints n →
              affSpace z W = affSpace z₀ W ∧
              (affHullInt z W).direction ≤ W ∧
              (affHullInt z W).direction =
                Submodule.span ℝ ((W : Set (EuclideanSpace ℝ (Fin n))) ∩ integralPoints n) ∧
              ((affHullInt z W : Set (EuclideanSpace ℝ (Fin n))) = affSpace z₀ (affHullInt z W).direction) := by
            clear * - n
            intro z z₀ W hz₀
            have hA : affSpace z W = affSpace z₀ W := by
              ext x
              have hz : z₀ - z ∈ W := hz₀.1
              constructor
              · intro hx
                show x - z₀ ∈ W
                have : x - z₀ = (x - z) - (z₀ - z) := by abel
                rw [this]; exact W.sub_mem hx hz
              · intro hx
                show x - z ∈ W
                have : x - z = (x - z₀) + (z₀ - z) := by abel
                rw [this]; exact W.add_mem hx hz
            have hdir : (affHullInt z W).direction =
                Submodule.span ℝ ((W : Set (EuclideanSpace ℝ (Fin n))) ∩ integralPoints n) := by
              unfold affHullInt
              rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ hz₀]
              congr 1
              ext x
              constructor
              · rintro ⟨y, ⟨hy, hyI⟩, rfl⟩
                rw [hA] at hy
                refine ⟨hy, fun i => ?_⟩
                obtain ⟨k, hk⟩ := hyI i
                obtain ⟨m, hm⟩ := hz₀.2 i
                refine ⟨k - m, ?_⟩
                show y.ofLp i - z₀.ofLp i = _
                rw [hk, hm]; push_cast; ring
              · rintro ⟨hx, hxI⟩
                refine ⟨x + z₀, ⟨?_, fun i => ?_⟩, ?_⟩
                · rw [hA]
                  show x + z₀ - z₀ ∈ W
                  rw [add_sub_cancel_right]; exact hx
                · obtain ⟨k, hk⟩ := hxI i
                  obtain ⟨m, hm⟩ := hz₀.2 i
                  refine ⟨k + m, ?_⟩
                  show x.ofLp i + z₀.ofLp i = _
                  rw [hk, hm]; push_cast; ring
                · show x + z₀ - z₀ = x
                  abel
            refine ⟨hA, ?_, hdir, ?_⟩
            · rw [hdir, Submodule.span_le]
              exact Set.inter_subset_left
            · ext x
              have hz₀V : z₀ ∈ affHullInt z W := subset_affineSpan ℝ _ hz₀
              constructor
              · intro hx
                exact AffineSubspace.vsub_mem_direction hx hz₀V
              · intro hx
                have : x = (x - z₀) +ᵥ z₀ := by simp
                rw [this]
                exact AffineSubspace.vadd_mem_of_mem_direction hx hz₀V
          obtain ⟨hA, hDW, hDspan, hV⟩ := base z z₀ W₀ hz₀
          have hiff : IsMaximalLatticeFree z W₀ S ↔ IsMaximalLatticeFree z₀ W₀ S := by
            unfold IsMaximalLatticeFree IsLatticeFree
            rw [hA]
          have hint : ∀ x ∈ affSpace z₀ W₀, x ∈ integralPoints n →
              x ∈ affSpace z₀ (affHullInt z W₀).direction := by
            intro x hx hxI
            rw [← hV]
            exact subset_affineSpan ℝ _ ⟨by rw [hA]; exact hx, hxI⟩
          rw [hiff, hV, hA]
          generalize (affHullInt z W₀).direction = D at *
          constructor
          · intro hmax
            by_cases h1 : ∃ p, p ∈ intRel (affSpace z₀ W₀) S
            · by_cases h2 : ∃ p ∈ affSpace z₀ D, p ∈ intRel (affSpace z₀ W₀) S
              · left
                obtain ⟨p, hpD, hp⟩ := h2
                exact case_a_fwd z₀ W₀ D S p hDW hint hp hpD hmax
              · right; right
                push Not at h2
                obtain ⟨p, hp⟩ := h1
                obtain ⟨a, b, hw, hSa, hDa⟩ := sep_aff z₀ W₀ D S p hDW hmax.1.1 hmax.1.2.1 hp h2
                refine ⟨a, b, hw, ?_, fun x hx => hDa x hx⟩
                exact (hmax.2 _ (half_lf z₀ W₀ a b hw fun x hx hxI => hDa x (hint x hx hxI))
                  (fun x hx => ⟨hmax.1.1 hx, hSa x hx⟩)).symm
            · right; left
              push Not at h1
              obtain ⟨v, hv, L, hL, hfr, hSL⟩ := hyper_of_empty z₀ W₀ S hW hmax.1.1 hmax.1.2.1 h1
              have hSe := hmax.2 _ (hyper_lf z₀ W₀ v L hv hL hfr) hSL
              rw [← hSe] at hmax
              obtain ⟨h3, h4⟩ := caseb_fwd z₀ W₀ D L v hz₀.2 hDspan hv hL hfr hmax
              exact ⟨v, hv, L, hL, hfr, hSe.symm, h3, h4⟩
          · rintro (⟨h1, h2, h3, h4, h5, h6, h7, -⟩ | ⟨v, hv, L, hL, hfr, rfl, h3, h4⟩ | ⟨a, b, hw, rfl, hV'⟩)
            · exact case_a_rev z₀ W₀ D S hDW hint h1 h2 h3 h4 h5 h6 h7
            · exact caseb_rev z₀ W₀ D L v hz₀.2 hDspan hv hL hfr h3 h4
            · exact half_max z₀ W₀ a b hz₀.2 hw fun x hx hxI => hV' (hint x hx hxI)
