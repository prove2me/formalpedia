-- Prove2me | solution 1 for MPECRelax.ScholtesConv.Supplement.theorem_3_12
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:27:57.214729+00:00
-- url     : https://prove2.me/submissions/3f81d5a7-4c23-4804-989f-7300141ce3fc

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC
import Definitions.Def_MPECRelax_ScholtesConv_Supplement_CQ
import Definitions.Def_MPECRelax_ScholtesConv_Scholtes
import Definitions.Def_MPECRelax_ScholtesConv_Supplement_SU

open Filter Topology Set

open MPECRelax
open MPECRelax.ScholtesConv
open MPECRelax.ScholtesConv.Supplement

theorem solution {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1)
    (θ : ℝ → ℝ) (hθ : IsSUTheta θ) (xs : E n)
    (hxs : P.Feasible xs) (hLICQ : MPEC_LICQ P xs) :
    ∃ N ∈ 𝓝 xs, ∀ t : ℝ, 0 < t → ∀ x ∈ N, (RSU P θ t).Feasible x →
      IPhiSU P θ x t ∩ (P.IG x ∪ P.IH x) = ∅ → IsLICQ (RSU P θ t) x := by
        classical
        let D : Set ℝ := Icc (-1) 1
        let d : ℝ → ℝ := derivWithin θ D
        have hD : UniqueDiffOn ℝ D := uniqueDiffOn_Icc (by norm_num)
        have hc : ContDiffOn ℝ 2 θ D := hθ.1
        have hd : ContDiffOn ℝ 1 d D := hc.derivWithin hD (by norm_num)
        have hdcont : ContinuousOn d D := hd.continuousOn
        have hinterior : interior D = Ioo (-1 : ℝ) 1 := interior_Icc
        have hderiv (u : ℝ) (hu : u ∈ Ioo (-1 : ℝ) 1) :
            deriv d u = iteratedDerivWithin 2 θ D u := by
          rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDerivWithin_succ,
            iteratedDerivWithin_one]
          exact (derivWithin_of_mem_nhds (by rw [← hinterior] at hu; exact mem_interior_iff_mem_nhds.mp hu)).symm
        have hdmono : StrictMonoOn d D := by
          apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hdcont
          intro u hu
          rw [hinterior] at hu
          rw [hderiv u hu]
          exact hθ.2.2.2.2.2.2.2 u hu
        have hdm : d (-1) = -1 := hθ.2.2.2.1
        have hdp : d 1 = 1 := hθ.2.2.2.2.1
        have hdint (u : ℝ) (hu : u ∈ Ioo (-1 : ℝ) 1) : -1 < d u ∧ d u < 1 := by
          constructor
          · simpa [hdm] using hdmono (show (-1 : ℝ) ∈ D by constructor <;> norm_num)
              ⟨hu.1.le, hu.2.le⟩ hu.1
          · simpa [hdp] using hdmono ⟨hu.1.le, hu.2.le⟩
              (show (1 : ℝ) ∈ D by constructor <;> norm_num) hu.2
        have hθderiv (u : ℝ) (hu : u ∈ Ioo (-1 : ℝ) 1) : deriv θ u = d u := by
          exact (derivWithin_of_mem_nhds (by rw [← hinterior] at hu; exact mem_interior_iff_mem_nhds.mp hu)).symm
        have hθdiff (u : ℝ) (hu : u ∈ Ioo (-1 : ℝ) 1) : DifferentiableAt ℝ θ u := by
          exact (hc.differentiableOn (by norm_num) u ⟨hu.1.le, hu.2.le⟩).differentiableAt
            (by rw [← hinterior] at hu; exact mem_interior_iff_mem_nhds.mp hu)
        have hplus : StrictMonoOn (fun u => θ u + u) D := by
          apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (hc.continuousOn.add continuousOn_id)
          intro u hu
          rw [hinterior] at hu
          change 0 < deriv (fun u => θ u + u) u
          have he : deriv (fun u => θ u + u) u = d u + 1 := by
            simpa only [Pi.add_def, id_eq, hθderiv u hu] using ((hθdiff u hu).hasDerivAt.add (hasDerivAt_id u)).deriv
          rw [he]
          linarith [(hdint u hu).1]
        have hminus : StrictMonoOn (fun u => u - θ u) D := by
          apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuousOn_id.sub hc.continuousOn)
          intro u hu
          rw [hinterior] at hu
          change 0 < deriv (fun u => u - θ u) u
          have he : deriv (fun u => u - θ u) u = 1 - d u := by
            simpa only [Pi.sub_def, id_eq, hθderiv u hu] using ((hasDerivAt_id u).sub (hθdiff u hu).hasDerivAt).deriv
          rw [he]
          linarith [(hdint u hu).2]
        have hpluszero (u : ℝ) (hu : u ∈ D) (hz : θ u + u = 0) : u = -1 := by
          by_contra hn
          have hh := hplus (show (-1 : ℝ) ∈ D by constructor <;> norm_num) hu
            (lt_of_le_of_ne hu.1 (Ne.symm hn))
          change θ (-1) + (-1) < θ u + u at hh
          rw [hθ.2.1, hz] at hh
          linarith
        have hminuszero (u : ℝ) (hu : u ∈ D) (hz : θ u - u = 0) : u = 1 := by
          by_contra hn
          have hh := hminus hu (show (1 : ℝ) ∈ D by constructor <;> norm_num)
            (lt_of_le_of_ne hu.2 hn)
          change u - θ u < 1 - θ 1 at hh
          rw [hθ.2.2.1] at hh
          linarith
        have hGmem (i : Fin l) (hi : i ∈ P.IG xs) : i ∈ P.I0p xs ∪ P.I00 xs := by
          change P.G i xs = 0 at hi
          rcases eq_or_lt_of_le (hxs.2.2 i).2.1 with hh | hh
          · exact Or.inr ⟨hi, hh.symm⟩
          · exact Or.inl ⟨hi, hh⟩
        have hHmem (i : Fin l) (hi : i ∈ P.IH xs) : i ∈ P.Ip0 xs ∪ P.I00 xs := by
          change P.H i xs = 0 at hi
          rcases eq_or_lt_of_le (hxs.2.2 i).1 with hg | hg
          · exact Or.inr ⟨hg.symm, hi⟩
          · exact Or.inl ⟨hg, hi⟩
        let B := ↥(P.Ig xs) ⊕ Fin p ⊕ ↥(P.IG xs) ⊕ ↥(P.IH xs)
        let b : B → E n := Sum.elim (fun i => gradient (P.g i) xs)
          (Sum.elim (fun i => gradient (P.h i) xs)
            (Sum.elim (fun i => gradient (P.G i) xs) (fun i => gradient (P.H i) xs)))
        let emb : B → ↥((P.TNLP xs).activeSet xs) ⊕
            (Fin p ⊕ ↥(P.I0p xs ∪ P.I00 xs) ⊕ ↥(P.Ip0 xs ∪ P.I00 xs)) :=
          Sum.elim (fun i => Sum.inl ⟨Sum.inl i, i.property⟩)
            (Sum.elim (fun i => Sum.inr (Sum.inl i))
              (Sum.elim (fun i => Sum.inr (Sum.inr (Sum.inl ⟨i, hGmem i i.property⟩)))
                (fun i => Sum.inr (Sum.inr (Sum.inr ⟨i, hHmem i i.property⟩)))))
        have hemb : Function.Injective emb := by
          intro a c he
          rcases a with a | a | a | a <;> rcases c with c | c | c | c <;>
            simp_all only [emb, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq,
              Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, Subtype.ext_iff]
          all_goals (have he' := Subtype.ext he; cases he'; rfl)
        have hb : LinearIndependent ℝ b := by
          convert hLICQ.comp emb hemb using 1
          ext i
          rcases i with i | i | i | i <;> rfl
        have hsum {q : Type} [Fintype q] (S : Set q) (a : q → ℝ) (v : q → E n)
            (ha : ∀ i ∉ S, a i = 0) : ∑ i : S, a i • v i = ∑ i, a i • v i := by
          have hz : ∑ i : ↥(Sᶜ), a i • v i = 0 := by
            apply Finset.sum_eq_zero
            intro i _
            rw [ha i i.property, zero_smul]
          have hh := Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ S) (fun i => a i • v i)
          change (∑ i : S, a i • v i) + (∑ i : ↥(Sᶜ), a i • v i) = _ at hh
          rw [hz, add_zero] at hh
          exact hh
        have hbase (a : Fin m → ℝ) (μ : Fin p → ℝ) (c e : Fin l → ℝ)
            (ha : ∀ i ∉ P.Ig xs, a i = 0) (hc : ∀ i ∉ P.IG xs, c i = 0)
            (he : ∀ i ∉ P.IH xs, e i = 0)
            (hz : (∑ i, a i • gradient (P.g i) xs) + (∑ i, μ i • gradient (P.h i) xs) +
              (∑ i, c i • gradient (P.G i) xs) + (∑ i, e i • gradient (P.H i) xs) = 0) :
            (∀ i, a i = 0) ∧ (∀ i, μ i = 0) ∧ (∀ i, c i = 0) ∧ (∀ i, e i = 0) := by
          let r : B → ℝ := Sum.elim (fun i => a i) (Sum.elim μ
            (Sum.elim (fun i => c i) (fun i => e i)))
          have hr : ∑ i, r i • b i = 0 := by
            simp only [B, r, b, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
            rw [hsum (P.Ig xs) a (fun i => gradient (P.g i) xs) ha,
              hsum (P.IG xs) c (fun i => gradient (P.G i) xs) hc,
              hsum (P.IH xs) e (fun i => gradient (P.H i) xs) he]
            simpa only [add_assoc] using hz
          have hr0 := Fintype.linearIndependent_iff.mp hb r hr
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro i
            by_cases hi : i ∈ P.Ig xs
            · exact hr0 (Sum.inl ⟨i, hi⟩)
            · exact ha i hi
          · intro i
            exact hr0 (Sum.inr (Sum.inl i))
          · intro i
            by_cases hi : i ∈ P.IG xs
            · exact hr0 (Sum.inr (Sum.inr (Sum.inl ⟨i, hi⟩)))
            · exact hc i hi
          · intro i
            by_cases hi : i ∈ P.IH xs
            · exact hr0 (Sum.inr (Sum.inr (Sum.inr ⟨i, hi⟩)))
            · exact he i hi
        let I := Fin m ⊕ Fin l ⊕ Fin l ⊕ Fin l
        let ig : Fin m → I := Sum.inl
        let iG : Fin l → I := fun i => Sum.inr (Sum.inl i)
        let iH : Fin l → I := fun i => Sum.inr (Sum.inr (Sum.inl i))
        let iφ : Fin l → I := fun i => Sum.inr (Sum.inr (Sum.inr i))
        let U := Fin l → D
        let v (x : E n) (u : U) : I → E n := Sum.elim (fun i => gradient (P.g i) x)
          (Sum.elim (fun i => -gradient (P.G i) x)
            (Sum.elim (fun i => -gradient (P.H i) x) (fun i =>
              (1 - d (u i)) • gradient (P.G i) x + (1 + d (u i)) • gradient (P.H i) x)))
        let C (S : Set I) (x : E n) (u : U) : Prop :=
          (∀ i, ig i ∈ S → P.g i x = 0) ∧
          (∀ i, iG i ∈ S → P.G i x = 0) ∧
          (∀ i, iH i ∈ S → P.H i x = 0) ∧
          (∀ i, iφ i ∈ S → P.G i x * (θ (u i) - (u i : ℝ)) =
            P.H i x * (θ (u i) + (u i : ℝ)))
        let V (S : Set I) (x : E n) (u : U) : (↥S ⊕ Fin p) → E n :=
          Sum.elim (fun i => v x u i) (fun j => gradient (P.h j) x)
        have hLI (S : Set I)
            (hS : ∀ i, iφ i ∈ S → iG i ∉ S ∧ iH i ∉ S)
            (u : U) (hC : C S xs u) : LinearIndependent ℝ (V S xs u) := by
          have hA (i : Fin l) (hi : iφ i ∈ S) (hn : i ∉ P.IG xs) : 1 - d (u i) = 0 := by
            have hg : P.G i xs ≠ 0 := hn
            have hh : P.H i xs = 0 := (mul_eq_zero.mp (hxs.2.2 i).2.2).resolve_left hg
            have hz := hC.2.2.2 i hi
            rw [hh, zero_mul] at hz
            have hu := hminuszero (u i) (u i).property ((mul_eq_zero.mp hz).resolve_left hg)
            rw [hu, hdp]
            norm_num
          have hB (i : Fin l) (hi : iφ i ∈ S) (hn : i ∉ P.IH xs) : 1 + d (u i) = 0 := by
            have hh : P.H i xs ≠ 0 := hn
            have hg : P.G i xs = 0 := (mul_eq_zero.mp (hxs.2.2 i).2.2).resolve_right hh
            have hz := hC.2.2.2 i hi
            rw [hg, zero_mul] at hz
            have hu := hpluszero (u i) (u i).property ((mul_eq_zero.mp hz.symm).resolve_left hh)
            rw [hu, hdm]
            norm_num
          rw [Fintype.linearIndependent_iff]
          intro r hr
          let a : I → ℝ := fun i => if hi : i ∈ S then r (Sum.inl ⟨i, hi⟩) else 0
          have ha (i : I) (hi : i ∉ S) : a i = 0 := dif_neg hi
          have hamem (i : I) (hi : i ∈ S) : a i = r (Sum.inl ⟨i, hi⟩) := dif_pos hi
          have hag (i : Fin m) (hi : i ∉ P.Ig xs) : a (ig i) = 0 := by
            apply ha
            intro hh
            exact hi (hC.1 i hh)
          have haG (i : Fin l) (hi : i ∉ P.IG xs) : a (iG i) = 0 := by
            apply ha
            intro hh
            exact hi (hC.2.1 i hh)
          have haH (i : Fin l) (hi : i ∉ P.IH xs) : a (iH i) = 0 := by
            apply ha
            intro hh
            exact hi (hC.2.2.1 i hh)
          have hc0 (i : Fin l) (hi : i ∉ P.IG xs) :
              -a (iG i) + a (iφ i) * (1 - d (u i)) = 0 := by
            rw [haG i hi]
            by_cases hh : iφ i ∈ S
            · rw [hA i hh hi]; ring
            · rw [ha _ hh]; ring
          have he0 (i : Fin l) (hi : i ∉ P.IH xs) :
              -a (iH i) + a (iφ i) * (1 + d (u i)) = 0 := by
            rw [haH i hi]
            by_cases hh : iφ i ∈ S
            · rw [hB i hh hi]; ring
            · rw [ha _ hh]; ring
          have hsumS : (∑ i : S, a i • v xs u i) = ∑ i, a i • v xs u i :=
            hsum S a (v xs u) ha
          have hh : (∑ i : I, a i • v xs u i) +
              (∑ j, r (Sum.inr j) • gradient (P.h j) xs) = 0 := by
            rw [← hsumS]
            simpa only [V, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, a, Subtype.coe_prop, dif_pos] using hr
          have hz : (∑ i, a (ig i) • gradient (P.g i) xs) +
              (∑ j, r (Sum.inr j) • gradient (P.h j) xs) +
              (∑ i, (-a (iG i) + a (iφ i) * (1 - d (u i))) • gradient (P.G i) xs) +
              (∑ i, (-a (iH i) + a (iφ i) * (1 + d (u i))) • gradient (P.H i) xs) = 0 := by
            simp only [I, v, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
              smul_add, smul_neg, smul_smul, Finset.sum_add_distrib] at hh
            simp only [ig, iG, iH, iφ, add_smul, neg_smul, Finset.sum_add_distrib]
            convert hh using 1 <;> abel
          obtain ⟨hg0, hμ0, hG0, hH0⟩ := hbase (fun i => a (ig i)) (fun j => r (Sum.inr j))
            (fun i => -a (iG i) + a (iφ i) * (1 - d (u i)))
            (fun i => -a (iH i) + a (iφ i) * (1 + d (u i))) hag hc0 he0 hz
          have hφ0 (i : Fin l) : a (iφ i) = 0 := by
            by_cases hi : iφ i ∈ S
            · have h1 := hG0 i
              have h2 := hH0 i
              rw [ha _ (hS i hi).1] at h1
              rw [ha _ (hS i hi).2] at h2
              nlinarith
            · exact ha _ hi
          intro j
          rcases j with ⟨j, hj⟩ | j
          · rw [← hamem j hj]
            rcases j with j | j | j | j
            · exact hg0 j
            · have hh := hG0 j
              rw [hφ0 j] at hh
              simpa only [zero_mul, add_zero, neg_eq_zero] using hh
            · have hh := hH0 j
              rw [hφ0 j] at hh
              simpa only [zero_mul, add_zero, neg_eq_zero] using hh
            · exact hφ0 j
          · exact hμ0 j
        have hgradcont (f : E n → ℝ) (hf : ContDiff ℝ 1 f) : Continuous (gradient f) := by
          exact (InnerProductSpace.toDual ℝ (E n)).symm.continuous.comp
            (hf.continuous_fderiv (by norm_num))
        have hdc (i : Fin l) : Continuous (fun u : U => d (u i)) :=
          (continuousOn_iff_continuous_domRestrict.mp hdcont).comp (continuous_apply i)
        have htc (i : Fin l) : Continuous (fun u : U => θ (u i)) :=
          (continuousOn_iff_continuous_domRestrict.mp hc.continuousOn).comp (continuous_apply i)
        have huc (i : Fin l) : Continuous (fun u : U => (u i : ℝ)) :=
          continuous_subtype_val.comp (continuous_apply i)
        have hCclosed (S : Set I) : IsClosed {z : E n × U | C S z.1 z.2} := by
          simp only [C, ofPred_and, ofPred_forall]
          exact (isClosed_iInter fun i => isClosed_iInter fun _ =>
            isClosed_eq ((hP.2.1 i).continuous.comp continuous_fst) continuous_const).inter
            ((isClosed_iInter fun i => isClosed_iInter fun _ =>
              isClosed_eq ((hP.2.2.2.1 i).continuous.comp continuous_fst) continuous_const).inter
            ((isClosed_iInter fun i => isClosed_iInter fun _ =>
              isClosed_eq ((hP.2.2.2.2 i).continuous.comp continuous_fst) continuous_const).inter
            (isClosed_iInter fun i => isClosed_iInter fun _ =>
              isClosed_eq
                (((hP.2.2.2.1 i).continuous.comp continuous_fst).mul
                  ((htc i).comp continuous_snd |>.sub ((huc i).comp continuous_snd)))
                (((hP.2.2.2.2 i).continuous.comp continuous_fst).mul
                  ((htc i).comp continuous_snd |>.add ((huc i).comp continuous_snd))))))
        have hVcont (S : Set I) : Continuous (fun z : E n × U => V S z.1 z.2) := by
          apply continuous_pi
          intro j
          rcases j with ⟨j, hj⟩ | j
          · rcases j with j | j | j | j
            · exact (hgradcont _ (hP.2.1 j)).comp continuous_fst
            · exact ((hgradcont _ (hP.2.2.2.1 j)).comp continuous_fst).neg
            · exact ((hgradcont _ (hP.2.2.2.2 j)).comp continuous_fst).neg
            · exact ((continuous_const.sub ((hdc j).comp continuous_snd)).smul
                ((hgradcont _ (hP.2.2.2.1 j)).comp continuous_fst)).add
                ((continuous_const.add ((hdc j).comp continuous_snd)).smul
                ((hgradcont _ (hP.2.2.2.2 j)).comp continuous_fst))
          · exact (hgradcont _ (hP.2.2.1 j)).comp continuous_fst
        haveI : CompactSpace D := isCompact_iff_compactSpace.mp (show IsCompact D from isCompact_Icc)
        have hlocal (S : Set I) (hS : ∀ i, iφ i ∈ S → iG i ∉ S ∧ iH i ∉ S) :
            ∀ᶠ x in 𝓝 xs, ∀ u : U, C S x u → LinearIndependent ℝ (V S x u) := by
          let Z : Set (E n × U) := {z | C S z.1 z.2} ∩
            {z | ¬ LinearIndependent ℝ (V S z.1 z.2)}
          have hZ : IsClosed Z := (hCclosed S).inter
            ((isOpen_setOfPred_linearIndependent.preimage (hVcont S)).isClosed_compl)
          have hclosed : IsClosed (Prod.fst '' Z) := isClosedMap_fst_of_compactSpace Z hZ
          have hx : xs ∉ Prod.fst '' Z := by
            rintro ⟨⟨x,u⟩, ⟨h1,h2⟩, heq⟩
            change x = xs at heq
            subst x
            exact h2 (hLI S hS u h1)
          filter_upwards [hclosed.isOpen_compl.mem_nhds hx] with x hx u hu
          by_contra hn
          exact hx ⟨(x,u), ⟨hu, hn⟩, rfl⟩
        have hlocalall : ∀ᶠ x in 𝓝 xs, ∀ S : Set I,
            (∀ i, iφ i ∈ S → iG i ∉ S ∧ iH i ∉ S) →
            ∀ u : U, C S x u → LinearIndependent ℝ (V S x u) := by
          rw [Filter.eventually_all]
          intro S
          by_cases hS : ∀ i, iφ i ∈ S → iG i ∉ S ∧ iH i ∉ S
          · exact (hlocal S hS).mono (fun x hx _ => hx)
          · exact Filter.Eventually.of_forall (fun x h => (hS h).elim)
        have hgradphi (f g : E n → ℝ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
            (x : E n) (t : ℝ) (ht : 0 < t) (hsmall : |f x - g x| < t) :
            gradient (fun y => PhiSU θ (f y) (g y) t) x =
              (1 - d ((f x - g x) / t)) • gradient f x +
              (1 + d ((f x - g x) / t)) • gradient g x := by
          have hz : (f x - g x) / t ∈ Ioo (-1 : ℝ) 1 := by
            rcases abs_lt.mp hsmall with ⟨h1,h2⟩
            constructor
            · rw [lt_div_iff₀ ht]; linarith
            · rw [div_lt_iff₀ ht]; linarith
          have he : (fun y => PhiSU θ (f y) (g y) t) =ᶠ[𝓝 x]
              (fun y => f y + g y - t * θ ((f y - g y) / t)) := by
            filter_upwards [((hf.continuous.sub hg.continuous).abs.tendsto x).eventually
              (gt_mem_nhds hsmall)] with y hy
            change |f y - g y| < t at hy
            simp only [PhiSU, phiSU, if_neg (not_le.mpr hy)]
          have hff := (hf.differentiable (by norm_num) x).hasFDerivAt
          have hgg := (hg.differentiable (by norm_num) x).hasFDerivAt
          have hdiv : HasFDerivAt (fun y => (f y - g y) / t)
              (t⁻¹ • (fderiv ℝ f x - fderiv ℝ g x)) x := by
            simpa only [Pi.sub_apply, div_eq_mul_inv, mul_comm] using (hff.sub hgg).const_mul t⁻¹
          have hθat : HasDerivAt θ (d ((f x - g x) / t)) ((f x - g x) / t) := by
            rw [← hθderiv _ hz]
            exact (hθdiff _ hz).hasDerivAt
          have hwhole := (hff.add hgg).sub ((hθat.comp_hasFDerivAt x hdiv).const_mul t)
          rw [he.gradient_eq]
          change (InnerProductSpace.toDual ℝ (E n)).symm
            (fderiv ℝ (fun y => f y + g y - t * θ ((f y - g y) / t)) x) = _
          rw [show fderiv ℝ (fun y => f y + g y - t * θ ((f y - g y) / t)) x =
              (fderiv ℝ f x + fderiv ℝ g x) -
              t • (d ((f x - g x) / t) • (t⁻¹ • (fderiv ℝ f x - fderiv ℝ g x))) from
            hwhole.fderiv]
          simp only [map_sub, map_add, map_smul, smul_smul]
          have ht0 : t ≠ 0 := ne_of_gt ht
          have hcanc : t * (d ((f x - g x) / t) * t⁻¹) = d ((f x - g x) / t) := by
            field_simp
          rw [hcanc]
          change gradient f x + gradient g x - d ((f x - g x) / t) •
            (gradient f x - gradient g x) = _
          module
        refine ⟨{x | ∀ S : Set I, (∀ i, iφ i ∈ S → iG i ∉ S ∧ iH i ∉ S) →
            ∀ u : U, C S x u → LinearIndependent ℝ (V S x u)}, hlocalall, ?_⟩
        intro t ht x hx hfeas hdisj
        let S : Set I := (RSU P θ t).activeSet x
        have hφ (i : Fin l) (hi : iφ i ∈ S) : i ∈ IPhiSU P θ x t := hi
        have hnot (i : Fin l) (hi : iφ i ∈ S) : P.G i x ≠ 0 ∧ P.H i x ≠ 0 := by
          constructor
          · intro hg
            have hm : i ∈ IPhiSU P θ x t ∩ (P.IG x ∪ P.IH x) := ⟨hφ i hi, Or.inl hg⟩
            rw [hdisj] at hm
            exact hm
          · intro hh
            have hm : i ∈ IPhiSU P θ x t ∩ (P.IG x ∪ P.IH x) := ⟨hφ i hi, Or.inr hh⟩
            rw [hdisj] at hm
            exact hm
        have hS : ∀ i, iφ i ∈ S → iG i ∉ S ∧ iH i ∉ S := by
          intro i hi
          constructor
          · intro hg
            exact (hnot i hi).1 (neg_eq_zero.mp hg)
          · intro hh
            exact (hnot i hi).2 (neg_eq_zero.mp hh)
        have hpos (i : Fin l) (hi : iφ i ∈ S) : 0 < P.G i x ∧ 0 < P.H i x := by
          have hg := hfeas.1 (iG i)
          have hh := hfeas.1 (iH i)
          change -P.G i x ≤ 0 at hg
          change -P.H i x ≤ 0 at hh
          have hn := hnot i hi
          exact ⟨lt_of_le_of_ne (neg_nonpos.mp hg) (Ne.symm hn.1),
            lt_of_le_of_ne (neg_nonpos.mp hh) (Ne.symm hn.2)⟩
        have hsmall (i : Fin l) (hi : iφ i ∈ S) : |P.G i x - P.H i x| < t := by
          by_contra hn
          have hbig : t ≤ |P.G i x - P.H i x| := le_of_not_gt hn
          have hh : PhiSU θ (P.G i x) (P.H i x) t = 0 := hi
          simp only [PhiSU, phiSU, if_pos hbig] at hh
          rcases le_total (P.G i x) (P.H i x) with hle | hle
          · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hh
            linarith [(hpos i hi).1]
          · rw [abs_of_nonneg (sub_nonneg.mpr hle)] at hh
            linarith [(hpos i hi).2]
        let u : U := fun i => if hi : iφ i ∈ S then
            ⟨(P.G i x - P.H i x) / t, by
              rcases abs_lt.mp (hsmall i hi) with ⟨h1,h2⟩
              constructor
              · apply le_of_lt; rw [lt_div_iff₀ ht]; linarith
              · apply le_of_lt; rw [div_lt_iff₀ ht]; linarith⟩
          else ⟨0, by constructor <;> norm_num⟩
        have hu (i : Fin l) (hi : iφ i ∈ S) : (u i : ℝ) = (P.G i x - P.H i x) / t := by
          simp only [u, dif_pos hi]
        have hC : C S x u := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro i hi; exact hi
          · intro i hi; exact neg_eq_zero.mp hi
          · intro i hi; exact neg_eq_zero.mp hi
          · intro i hi
            rw [hu i hi]
            have hh : PhiSU θ (P.G i x) (P.H i x) t = 0 := hi
            simp only [PhiSU, phiSU, if_neg (not_le.mpr (hsmall i hi))] at hh
            have ht0 : t ≠ 0 := ne_of_gt ht
            have hh' : t * θ ((P.G i x - P.H i x) / t) = P.G i x + P.H i x := by
              linarith only [hh]
            field_simp
            rw [hh']
            ring
        have hv := hx S hS u hC
        change LinearIndependent ℝ _
        convert hv using 1
        apply funext
        intro j
        rcases j with ⟨j,hj⟩ | j
        · rcases j with j | j | j | j
          · rfl
          · change gradient (fun y => -P.G j y) x = -gradient (P.G j) x
            simp only [gradient, fderiv_fun_neg, map_neg]
          · change gradient (fun y => -P.H j y) x = -gradient (P.H j) x
            simp only [gradient, fderiv_fun_neg, map_neg]
          · change gradient (fun y => PhiSU θ (P.G j y) (P.H j y) t) x =
              (1 - d (u j)) • gradient (P.G j) x + (1 + d (u j)) • gradient (P.H j) x
            rw [hu j hj]
            exact hgradphi _ _ (hP.2.2.2.1 j) (hP.2.2.2.2 j) x t ht (hsmall j hj)
        · rfl
