-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part02_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:03:42.590987+00:00
-- url     : https://prove2.me/submissions/2bfa6d57-a9df-4300-b776-5d1233a2d310

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
import Definitions.Def_Snaky21Calc11Part01
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part01_valid
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate
namespace OAI.Snaky21
theorem base_valid (i : Fin 6) : Valid (baseCard i) := claim_calculus.1 i
theorem placed_valid (r : Fin 8) (t : Cell) {c : Card} (h : Valid c) : Valid (placed r t c) := claim_calculus.2.1 r t c h
end OAI.Snaky21

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace OAI.Snaky21.Certificate
theorem computed_card_ext {c d : Card} (hA : c.required = d.required) (hT : c.envelope = d.envelope) (hh : c.height = d.height) : c = d := by
  cases c
  cases d
  cases hA
  cases hT
  cases hh
  rfl
theorem valid_4 : Valid card_4 := block00_valid.2.2.2.2.1
theorem valid_9 : Valid card_9 := block00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_15 : Valid card_15 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_22 : Valid card_22 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_30 : Valid card_30 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_59 : Valid card_59 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_65 : Valid card_65 := block01_valid.2.1
theorem valid_66 : Valid card_66 := block01_valid.2.2.1
theorem valid_74 : Valid card_74 := block01_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_152 : Valid card_152 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_154 : Valid card_154 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_159 : Valid card_159 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_166 : Valid card_166 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_238 : Valid card_238 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_261 : Valid card_261 := block04_valid.2.2.2.2.2.1
theorem valid_296 : Valid card_296 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_318 : Valid card_318 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_325 : Valid card_325 := block05_valid.2.2.2.2.2.1
theorem valid_334 : Valid card_334 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_379 : Valid card_379 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_394 : Valid card_394 := block06_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_417 : Valid card_417 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_420 : Valid card_420 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_512 : Valid card_512 := block08_valid.1
theorem valid_517 : Valid card_517 := block08_valid.2.2.2.2.2.1
theorem valid_526 : Valid card_526 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_527 : Valid card_527 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_532 : Valid card_532 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_537 : Valid card_537 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_603 : Valid card_603 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem calc11_card_198_eq : placed 2 (3, 4) card_4 = calc11_card_198 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_199_eq : placed 1 (2, 3) card_9 = calc11_card_199 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_200_eq : calc11_card_199.required ∪ ∅ = calc11_set_200 := by decide +kernel

theorem calc11_set_201_eq : calc11_card_199.envelope ∪ ∅ = calc11_set_201 := by decide +kernel

theorem calc11_set_202_eq : calc11_card_198.required ∪ calc11_set_200 = calc11_set_202 := by decide +kernel

theorem calc11_set_203_eq : calc11_card_198.envelope ∪ calc11_set_201 = calc11_set_203 := by decide +kernel

theorem calc11_set_204_eq : calc11_card_199.envelope ∩ calc11_card_198.envelope = calc11_set_204 := by decide +kernel

theorem calc11_set_205_eq : calc11_set_202 ∪ calc11_set_204 = calc11_set_205 := by decide +kernel

theorem calc11_finishA_206 : calc11_set_205.erase (6, 4) = inline_805.required := by decide +kernel

theorem calc11_finishT_206 : insert (6, 4) calc11_set_203 = inline_805.envelope := by decide +kernel

theorem eq_inline_805 : inline_805 = combine (6, 4) [placed 2 (3, 4) card_4, placed 1 (2, 3) card_9] := by
  rw [calc11_card_198_eq, calc11_card_199_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_200_eq, calc11_set_202_eq, calc11_set_204_eq, calc11_set_205_eq, calc11_finishA_206]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_201_eq, calc11_set_203_eq, calc11_finishT_206]
  · decide +kernel

theorem valid_inline_805 : Valid inline_805 := by
  rw [eq_inline_805]
  apply combination_rule (6, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 4) valid_4
  subst c
  exact placed_valid 1 (2, 3) valid_9

theorem calc11_card_207_eq : placed 5 (3, 4) card_154 = calc11_card_207 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_208_eq : placed 2 (3, 6) card_159 = calc11_card_208 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_209_eq : calc11_card_208.required ∪ ∅ = calc11_set_209 := by decide +kernel

theorem calc11_set_210_eq : calc11_card_208.envelope ∪ ∅ = calc11_set_210 := by decide +kernel

theorem calc11_set_211_eq : calc11_card_207.required ∪ calc11_set_209 = calc11_set_211 := by decide +kernel

theorem calc11_set_212_eq : calc11_card_207.envelope ∪ calc11_set_210 = calc11_set_212 := by decide +kernel

theorem calc11_set_213_eq : calc11_card_208.envelope ∩ calc11_card_207.envelope = calc11_set_213 := by decide +kernel

theorem calc11_set_214_eq : calc11_set_211 ∪ calc11_set_213 = calc11_set_214 := by decide +kernel

theorem calc11_finishA_215 : calc11_set_214.erase (5, 3) = inline_806.required := by decide +kernel

theorem calc11_finishT_215 : insert (5, 3) calc11_set_212 = inline_806.envelope := by decide +kernel

theorem eq_inline_806 : inline_806 = combine (5, 3) [placed 5 (3, 4) card_154, placed 2 (3, 6) card_159] := by
  rw [calc11_card_207_eq, calc11_card_208_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_209_eq, calc11_set_211_eq, calc11_set_213_eq, calc11_set_214_eq, calc11_finishA_215]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_210_eq, calc11_set_212_eq, calc11_finishT_215]
  · decide +kernel

theorem valid_inline_806 : Valid inline_806 := by
  rw [eq_inline_806]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 4) valid_154
  subst c
  exact placed_valid 2 (3, 6) valid_159

theorem calc11_card_216_eq : placed 5 (3, 5) card_22 = calc11_card_216 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_217_eq : placed 4 (8, 2) card_152 = calc11_card_217 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_218_eq : placed 0 (4, 1) card_166 = calc11_card_218 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_219_eq : calc11_card_218.required ∪ ∅ = calc11_set_219 := by decide +kernel

theorem calc11_set_220_eq : calc11_card_218.envelope ∪ ∅ = calc11_set_220 := by decide +kernel

theorem calc11_set_221_eq : calc11_card_217.required ∪ calc11_set_219 = calc11_set_221 := by decide +kernel

theorem calc11_set_222_eq : calc11_card_217.envelope ∪ calc11_set_220 = calc11_set_222 := by decide +kernel

theorem calc11_set_223_eq : calc11_card_216.required ∪ calc11_set_221 = calc11_set_223 := by decide +kernel

theorem calc11_set_224_eq : calc11_card_216.envelope ∪ calc11_set_222 = calc11_set_224 := by decide +kernel

theorem calc11_set_225_eq : calc11_card_218.envelope ∩ calc11_card_216.envelope = calc11_set_225 := by decide +kernel

theorem calc11_set_226_eq : calc11_card_217.envelope ∩ calc11_set_225 = calc11_set_226 := by decide +kernel

theorem calc11_set_227_eq : calc11_set_223 ∪ calc11_set_226 = calc11_set_227 := by decide +kernel

theorem calc11_finishA_228 : calc11_set_227.erase (7, 5) = inline_807.required := by decide +kernel

theorem calc11_finishT_228 : insert (7, 5) calc11_set_224 = inline_807.envelope := by decide +kernel

theorem eq_inline_807 : inline_807 = combine (7, 5) [placed 5 (3, 5) card_22, placed 4 (8, 2) card_152, placed 0 (4, 1) card_166] := by
  rw [calc11_card_216_eq, calc11_card_217_eq, calc11_card_218_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_219_eq, calc11_set_221_eq, calc11_set_223_eq, calc11_set_225_eq, calc11_set_226_eq, calc11_set_227_eq, calc11_finishA_228]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_220_eq, calc11_set_222_eq, calc11_set_224_eq, calc11_finishT_228]
  · decide +kernel

theorem valid_inline_807 : Valid inline_807 := by
  rw [eq_inline_807]
  apply combination_rule (7, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 5) valid_22
  rcases hc with rfl | hc
  · exact placed_valid 4 (8, 2) valid_152
  subst c
  exact placed_valid 0 (4, 1) valid_166

theorem calc11_card_229_eq : placed 5 (3, 4) card_261 = calc11_card_229 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_230_eq : inline_807.required ∪ ∅ = calc11_set_230 := by decide +kernel

theorem calc11_set_231_eq : inline_807.envelope ∪ ∅ = calc11_set_231 := by decide +kernel

theorem calc11_set_232_eq : inline_806.required ∪ calc11_set_230 = calc11_set_232 := by decide +kernel

theorem calc11_set_233_eq : inline_806.envelope ∪ calc11_set_231 = calc11_set_233 := by decide +kernel

theorem calc11_set_234_eq : inline_805.required ∪ calc11_set_232 = calc11_set_234 := by decide +kernel

theorem calc11_set_235_eq : inline_805.envelope ∪ calc11_set_233 = calc11_set_235 := by decide +kernel

theorem calc11_set_236_eq : calc11_card_229.required ∪ calc11_set_234 = calc11_set_236 := by decide +kernel

theorem calc11_set_237_eq : calc11_card_229.envelope ∪ calc11_set_235 = calc11_set_237 := by decide +kernel

theorem calc11_set_238_eq : inline_807.envelope ∩ calc11_card_229.envelope = calc11_set_238 := by decide +kernel

theorem calc11_set_239_eq : inline_806.envelope ∩ calc11_set_238 = calc11_set_239 := by decide +kernel

theorem calc11_set_240_eq : inline_805.envelope ∩ calc11_set_239 = calc11_set_240 := by decide +kernel

theorem calc11_set_241_eq : calc11_set_236 ∪ calc11_set_240 = calc11_set_241 := by decide +kernel

theorem calc11_finishA_242 : calc11_set_241.erase (7, 3) = inline_808.required := by decide +kernel

theorem calc11_finishT_242 : insert (7, 3) calc11_set_237 = inline_808.envelope := by decide +kernel

theorem eq_inline_808 : inline_808 = combine (7, 3) [placed 5 (3, 4) card_261, inline_805, inline_806, inline_807] := by
  rw [calc11_card_229_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_230_eq, calc11_set_232_eq, calc11_set_234_eq, calc11_set_236_eq, calc11_set_238_eq, calc11_set_239_eq, calc11_set_240_eq, calc11_set_241_eq, calc11_finishA_242]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_231_eq, calc11_set_233_eq, calc11_set_235_eq, calc11_set_237_eq, calc11_finishT_242]
  · decide +kernel

theorem valid_inline_808 : Valid inline_808 := by
  rw [eq_inline_808]
  apply combination_rule (7, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 4) valid_261
  rcases hc with rfl | hc
  · exact valid_inline_805
  rcases hc with rfl | hc
  · exact valid_inline_806
  subst c
  exact valid_inline_807

theorem calc11_card_243_eq : placed 1 (2, 4) card_15 = calc11_card_243 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_244_eq : placed 5 (1, 5) card_65 = calc11_card_244 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_245_eq : inline_808.required ∪ ∅ = calc11_set_245 := by decide +kernel

theorem calc11_set_246_eq : inline_808.envelope ∪ ∅ = calc11_set_246 := by decide +kernel

theorem calc11_set_247_eq : calc11_card_244.required ∪ calc11_set_245 = calc11_set_247 := by decide +kernel

theorem calc11_set_248_eq : calc11_card_244.envelope ∪ calc11_set_246 = calc11_set_248 := by decide +kernel

theorem calc11_set_249_eq : calc11_card_243.required ∪ calc11_set_247 = calc11_set_249 := by decide +kernel

theorem calc11_set_250_eq : calc11_card_243.envelope ∪ calc11_set_248 = calc11_set_250 := by decide +kernel

theorem calc11_set_251_eq : inline_808.envelope ∩ calc11_card_243.envelope = calc11_set_251 := by decide +kernel

theorem calc11_set_252_eq : calc11_card_244.envelope ∩ calc11_set_251 = calc11_set_252 := by decide +kernel

theorem calc11_set_253_eq : calc11_set_249 ∪ calc11_set_252 = calc11_set_253 := by decide +kernel

theorem calc11_finishA_254 : calc11_set_253.erase (3, 4) = inline_809.required := by decide +kernel

theorem calc11_finishT_254 : insert (3, 4) calc11_set_250 = inline_809.envelope := by decide +kernel

theorem eq_inline_809 : inline_809 = combine (3, 4) [placed 1 (2, 4) card_15, placed 5 (1, 5) card_65, inline_808] := by
  rw [calc11_card_243_eq, calc11_card_244_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_245_eq, calc11_set_247_eq, calc11_set_249_eq, calc11_set_251_eq, calc11_set_252_eq, calc11_set_253_eq, calc11_finishA_254]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_246_eq, calc11_set_248_eq, calc11_set_250_eq, calc11_finishT_254]
  · decide +kernel

theorem valid_inline_809 : Valid inline_809 := by
  rw [eq_inline_809]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_15
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 5) valid_65
  subst c
  exact valid_inline_808

theorem calc11_card_255_eq : placed 1 (0, 3) card_318 = calc11_card_255 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_256_eq : placed 7 (7, 4) card_334 = calc11_card_256 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_257_eq : placed 5 (3, 5) card_379 = calc11_card_257 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_258_eq : calc11_card_257.required ∪ ∅ = calc11_set_258 := by decide +kernel

theorem calc11_set_259_eq : calc11_card_257.envelope ∪ ∅ = calc11_set_259 := by decide +kernel

theorem calc11_set_260_eq : calc11_card_256.required ∪ calc11_set_258 = calc11_set_260 := by decide +kernel

theorem calc11_set_261_eq : calc11_card_256.envelope ∪ calc11_set_259 = calc11_set_261 := by decide +kernel

theorem calc11_set_262_eq : calc11_card_255.required ∪ calc11_set_260 = calc11_set_262 := by decide +kernel

theorem calc11_set_263_eq : calc11_card_255.envelope ∪ calc11_set_261 = calc11_set_263 := by decide +kernel

theorem calc11_set_264_eq : calc11_card_257.envelope ∩ calc11_card_255.envelope = calc11_set_264 := by decide +kernel

theorem calc11_set_265_eq : calc11_card_256.envelope ∩ calc11_set_264 = calc11_set_265 := by decide +kernel

theorem calc11_set_266_eq : calc11_set_262 ∪ calc11_set_265 = calc11_set_266 := by decide +kernel

theorem calc11_finishA_267 : calc11_set_266.erase (3, 3) = inline_810.required := by decide +kernel

theorem calc11_finishT_267 : insert (3, 3) calc11_set_263 = inline_810.envelope := by decide +kernel

theorem eq_inline_810 : inline_810 = combine (3, 3) [placed 1 (0, 3) card_318, placed 7 (7, 4) card_334, placed 5 (3, 5) card_379] := by
  rw [calc11_card_255_eq, calc11_card_256_eq, calc11_card_257_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_258_eq, calc11_set_260_eq, calc11_set_262_eq, calc11_set_264_eq, calc11_set_265_eq, calc11_set_266_eq, calc11_finishA_267]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_259_eq, calc11_set_261_eq, calc11_set_263_eq, calc11_finishT_267]
  · decide +kernel

theorem valid_inline_810 : Valid inline_810 := by
  rw [eq_inline_810]
  apply combination_rule (3, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 3) valid_318
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 4) valid_334
  subst c
  exact placed_valid 5 (3, 5) valid_379

theorem calc11_card_268_eq : placed 7 (6, 5) card_66 = calc11_card_268 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_269_eq : placed 7 (6, 6) card_238 = calc11_card_269 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_270_eq : placed 5 (2, 5) card_394 = calc11_card_270 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_271_eq : calc11_card_270.required ∪ ∅ = calc11_set_271 := by decide +kernel

theorem calc11_set_272_eq : calc11_card_270.envelope ∪ ∅ = calc11_set_272 := by decide +kernel

theorem calc11_set_273_eq : calc11_card_269.required ∪ calc11_set_271 = calc11_set_273 := by decide +kernel

theorem calc11_set_274_eq : calc11_card_269.envelope ∪ calc11_set_272 = calc11_set_274 := by decide +kernel

theorem calc11_set_275_eq : calc11_card_268.required ∪ calc11_set_273 = calc11_set_275 := by decide +kernel

theorem calc11_set_276_eq : calc11_card_268.envelope ∪ calc11_set_274 = calc11_set_276 := by decide +kernel

theorem calc11_set_277_eq : calc11_card_270.envelope ∩ calc11_card_268.envelope = calc11_set_277 := by decide +kernel

theorem calc11_set_278_eq : calc11_card_269.envelope ∩ calc11_set_277 = calc11_set_278 := by decide +kernel

theorem calc11_set_279_eq : calc11_set_275 ∪ calc11_set_278 = calc11_set_279 := by decide +kernel

theorem calc11_finishA_280 : calc11_set_279.erase (3, 4) = inline_811.required := by decide +kernel

theorem calc11_finishT_280 : insert (3, 4) calc11_set_276 = inline_811.envelope := by decide +kernel

theorem eq_inline_811 : inline_811 = combine (3, 4) [placed 7 (6, 5) card_66, placed 7 (6, 6) card_238, placed 5 (2, 5) card_394] := by
  rw [calc11_card_268_eq, calc11_card_269_eq, calc11_card_270_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_271_eq, calc11_set_273_eq, calc11_set_275_eq, calc11_set_277_eq, calc11_set_278_eq, calc11_set_279_eq, calc11_finishA_280]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_272_eq, calc11_set_274_eq, calc11_set_276_eq, calc11_finishT_280]
  · decide +kernel

theorem valid_inline_811 : Valid inline_811 := by
  rw [eq_inline_811]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 5) valid_66
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 6) valid_238
  subst c
  exact placed_valid 5 (2, 5) valid_394

theorem calc11_card_281_eq : placed 7 (7, 5) card_417 = calc11_card_281 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_282_eq : placed 7 (6, 5) card_420 = calc11_card_282 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_283_eq : placed 7 (6, 5) card_526 = calc11_card_283 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_284_eq : placed 5 (0, 6) card_532 = calc11_card_284 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_285_eq : inline_811.required ∪ ∅ = calc11_set_285 := by decide +kernel

theorem calc11_set_286_eq : inline_811.envelope ∪ ∅ = calc11_set_286 := by decide +kernel

theorem calc11_set_287_eq : inline_810.required ∪ calc11_set_285 = calc11_set_287 := by decide +kernel

theorem calc11_set_288_eq : inline_810.envelope ∪ calc11_set_286 = calc11_set_288 := by decide +kernel

theorem calc11_set_289_eq : calc11_card_284.required ∪ calc11_set_287 = calc11_set_289 := by decide +kernel

theorem calc11_set_290_eq : calc11_card_284.envelope ∪ calc11_set_288 = calc11_set_290 := by decide +kernel

theorem calc11_set_291_eq : calc11_card_283.required ∪ calc11_set_289 = calc11_set_291 := by decide +kernel

theorem calc11_set_292_eq : calc11_card_283.envelope ∪ calc11_set_290 = calc11_set_292 := by decide +kernel

theorem calc11_set_293_eq : calc11_card_282.required ∪ calc11_set_291 = calc11_set_293 := by decide +kernel

theorem calc11_set_294_eq : calc11_card_282.envelope ∪ calc11_set_292 = calc11_set_294 := by decide +kernel

theorem calc11_set_295_eq : calc11_card_281.required ∪ calc11_set_293 = calc11_set_295 := by decide +kernel

theorem calc11_set_296_eq : calc11_card_281.envelope ∪ calc11_set_294 = calc11_set_296 := by decide +kernel

theorem calc11_set_297_eq : inline_811.envelope ∩ calc11_card_281.envelope = calc11_set_297 := by decide +kernel

theorem calc11_set_298_eq : inline_810.envelope ∩ calc11_set_297 = calc11_set_298 := by decide +kernel

theorem calc11_set_299_eq : calc11_card_284.envelope ∩ calc11_set_298 = calc11_set_299 := by decide +kernel

theorem calc11_set_300_eq : calc11_card_283.envelope ∩ calc11_set_299 = calc11_set_300 := by decide +kernel

theorem calc11_set_301_eq : calc11_card_282.envelope ∩ calc11_set_300 = calc11_set_301 := by decide +kernel

theorem calc11_set_302_eq : calc11_set_295 ∪ calc11_set_301 = calc11_set_302 := by decide +kernel

theorem calc11_finishA_303 : calc11_set_302.erase (5, 3) = inline_812.required := by decide +kernel

theorem calc11_finishT_303 : insert (5, 3) calc11_set_296 = inline_812.envelope := by decide +kernel

theorem eq_inline_812 : inline_812 = combine (5, 3) [placed 7 (7, 5) card_417, placed 7 (6, 5) card_420, placed 7 (6, 5) card_526, placed 5 (0, 6) card_532, inline_810, inline_811] := by
  rw [calc11_card_281_eq, calc11_card_282_eq, calc11_card_283_eq, calc11_card_284_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_285_eq, calc11_set_287_eq, calc11_set_289_eq, calc11_set_291_eq, calc11_set_293_eq, calc11_set_295_eq, calc11_set_297_eq, calc11_set_298_eq, calc11_set_299_eq, calc11_set_300_eq, calc11_set_301_eq, calc11_set_302_eq, calc11_finishA_303]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_286_eq, calc11_set_288_eq, calc11_set_290_eq, calc11_set_292_eq, calc11_set_294_eq, calc11_set_296_eq, calc11_finishT_303]
  · decide +kernel

theorem valid_inline_812 : Valid inline_812 := by
  rw [eq_inline_812]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (7, 5) valid_417
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 5) valid_420
  rcases hc with rfl | hc
  · exact placed_valid 7 (6, 5) valid_526
  rcases hc with rfl | hc
  · exact placed_valid 5 (0, 6) valid_532
  rcases hc with rfl | hc
  · exact valid_inline_810
  subst c
  exact valid_inline_811

theorem calc11_card_304_eq : placed 1 (4, 4) card_30 = calc11_card_304 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_305_eq : placed 0 (4, 1) card_59 = calc11_card_305 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_306_eq : placed 5 (3, 6) card_296 = calc11_card_306 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_307_eq : placed 0 (6, 1) card_603 = calc11_card_307 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_308_eq : calc11_card_307.required ∪ ∅ = calc11_set_308 := by decide +kernel

theorem calc11_set_309_eq : calc11_card_307.envelope ∪ ∅ = calc11_set_309 := by decide +kernel

theorem calc11_set_310_eq : calc11_card_306.required ∪ calc11_set_308 = calc11_set_310 := by decide +kernel

theorem calc11_set_311_eq : calc11_card_306.envelope ∪ calc11_set_309 = calc11_set_311 := by decide +kernel

theorem calc11_set_312_eq : calc11_card_305.required ∪ calc11_set_310 = calc11_set_312 := by decide +kernel

theorem calc11_set_313_eq : calc11_card_305.envelope ∪ calc11_set_311 = calc11_set_313 := by decide +kernel

theorem calc11_set_314_eq : calc11_card_304.required ∪ calc11_set_312 = calc11_set_314 := by decide +kernel

theorem calc11_set_315_eq : calc11_card_304.envelope ∪ calc11_set_313 = calc11_set_315 := by decide +kernel

theorem calc11_set_316_eq : calc11_card_307.envelope ∩ calc11_card_304.envelope = calc11_set_316 := by decide +kernel

theorem calc11_set_317_eq : calc11_card_306.envelope ∩ calc11_set_316 = calc11_set_317 := by decide +kernel

theorem calc11_set_318_eq : calc11_card_305.envelope ∩ calc11_set_317 = calc11_set_318 := by decide +kernel

theorem calc11_set_319_eq : calc11_set_314 ∪ calc11_set_318 = calc11_set_319 := by decide +kernel

theorem calc11_finishA_320 : calc11_set_319.erase (7, 4) = inline_813.required := by decide +kernel

theorem calc11_finishT_320 : insert (7, 4) calc11_set_315 = inline_813.envelope := by decide +kernel

theorem eq_inline_813 : inline_813 = combine (7, 4) [placed 1 (4, 4) card_30, placed 0 (4, 1) card_59, placed 5 (3, 6) card_296, placed 0 (6, 1) card_603] := by
  rw [calc11_card_304_eq, calc11_card_305_eq, calc11_card_306_eq, calc11_card_307_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_308_eq, calc11_set_310_eq, calc11_set_312_eq, calc11_set_314_eq, calc11_set_316_eq, calc11_set_317_eq, calc11_set_318_eq, calc11_set_319_eq, calc11_finishA_320]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_309_eq, calc11_set_311_eq, calc11_set_313_eq, calc11_set_315_eq, calc11_finishT_320]
  · decide +kernel

theorem valid_inline_813 : Valid inline_813 := by
  rw [eq_inline_813]
  apply combination_rule (7, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 4) valid_30
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 1) valid_59
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 6) valid_296
  subst c
  exact placed_valid 0 (6, 1) valid_603

theorem calc11_card_321_eq : placed 5 (3, 5) card_22 = calc11_card_321 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_322_eq : placed 5 (4, 5) card_74 = calc11_card_322 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_323_eq : placed 2 (3, 9) card_325 = calc11_card_323 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_324_eq : inline_813.required ∪ ∅ = calc11_set_324 := by decide +kernel

theorem calc11_set_325_eq : inline_813.envelope ∪ ∅ = calc11_set_325 := by decide +kernel

theorem calc11_set_326_eq : calc11_card_323.required ∪ calc11_set_324 = calc11_set_326 := by decide +kernel

theorem calc11_set_327_eq : calc11_card_323.envelope ∪ calc11_set_325 = calc11_set_327 := by decide +kernel

theorem calc11_set_328_eq : calc11_card_322.required ∪ calc11_set_326 = calc11_set_328 := by decide +kernel

theorem calc11_set_329_eq : calc11_card_322.envelope ∪ calc11_set_327 = calc11_set_329 := by decide +kernel

theorem calc11_set_330_eq : calc11_card_321.required ∪ calc11_set_328 = calc11_set_330 := by decide +kernel

theorem calc11_set_331_eq : calc11_card_321.envelope ∪ calc11_set_329 = calc11_set_331 := by decide +kernel

theorem calc11_set_332_eq : inline_813.envelope ∩ calc11_card_321.envelope = calc11_set_332 := by decide +kernel

theorem calc11_set_333_eq : calc11_card_323.envelope ∩ calc11_set_332 = calc11_set_333 := by decide +kernel

theorem calc11_set_334_eq : calc11_card_322.envelope ∩ calc11_set_333 = calc11_set_334 := by decide +kernel

theorem calc11_set_335_eq : calc11_set_330 ∪ calc11_set_334 = calc11_set_335 := by decide +kernel

theorem calc11_finishA_336 : calc11_set_335.erase (7, 5) = inline_814.required := by decide +kernel

theorem calc11_finishT_336 : insert (7, 5) calc11_set_331 = inline_814.envelope := by decide +kernel

theorem eq_inline_814 : inline_814 = combine (7, 5) [placed 5 (3, 5) card_22, placed 5 (4, 5) card_74, placed 2 (3, 9) card_325, inline_813] := by
  rw [calc11_card_321_eq, calc11_card_322_eq, calc11_card_323_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_324_eq, calc11_set_326_eq, calc11_set_328_eq, calc11_set_330_eq, calc11_set_332_eq, calc11_set_333_eq, calc11_set_334_eq, calc11_set_335_eq, calc11_finishA_336]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_325_eq, calc11_set_327_eq, calc11_set_329_eq, calc11_set_331_eq, calc11_finishT_336]
  · decide +kernel

theorem valid_inline_814 : Valid inline_814 := by
  rw [eq_inline_814]
  apply combination_rule (7, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 5) valid_22
  rcases hc with rfl | hc
  · exact placed_valid 5 (4, 5) valid_74
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 9) valid_325
  subst c
  exact valid_inline_813

theorem calc11_card_337_eq : placed 7 (8, 6) card_512 = calc11_card_337 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_338_eq : placed 5 (1, 6) card_517 = calc11_card_338 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_339_eq : placed 7 (8, 6) card_527 = calc11_card_339 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_340_eq : placed 7 (8, 6) card_537 = calc11_card_340 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_341_eq : inline_814.required ∪ ∅ = calc11_set_341 := by decide +kernel

theorem calc11_set_342_eq : inline_814.envelope ∪ ∅ = calc11_set_342 := by decide +kernel

theorem calc11_set_343_eq : inline_812.required ∪ calc11_set_341 = calc11_set_343 := by decide +kernel

theorem calc11_set_344_eq : inline_812.envelope ∪ calc11_set_342 = calc11_set_344 := by decide +kernel

theorem calc11_set_345_eq : inline_809.required ∪ calc11_set_343 = calc11_set_345 := by decide +kernel

theorem calc11_set_346_eq : inline_809.envelope ∪ calc11_set_344 = calc11_set_346 := by decide +kernel

theorem calc11_set_347_eq : calc11_card_340.required ∪ calc11_set_345 = calc11_set_347 := by decide +kernel

theorem calc11_set_348_eq : calc11_card_340.envelope ∪ calc11_set_346 = calc11_set_348 := by decide +kernel

theorem calc11_set_349_eq : calc11_card_339.required ∪ calc11_set_347 = calc11_set_349 := by decide +kernel

theorem calc11_set_350_eq : calc11_card_339.envelope ∪ calc11_set_348 = calc11_set_350 := by decide +kernel

theorem calc11_set_351_eq : calc11_card_338.required ∪ calc11_set_349 = calc11_set_351 := by decide +kernel

theorem calc11_set_352_eq : calc11_card_338.envelope ∪ calc11_set_350 = calc11_set_352 := by decide +kernel

theorem calc11_set_353_eq : calc11_card_337.required ∪ calc11_set_351 = calc11_set_353 := by decide +kernel

theorem calc11_set_354_eq : calc11_card_337.envelope ∪ calc11_set_352 = calc11_set_354 := by decide +kernel

theorem calc11_set_355_eq : inline_814.envelope ∩ calc11_card_337.envelope = calc11_set_355 := by decide +kernel

theorem calc11_set_356_eq : inline_812.envelope ∩ calc11_set_355 = calc11_set_356 := by decide +kernel

theorem calc11_set_357_eq : inline_809.envelope ∩ calc11_set_356 = calc11_set_357 := by decide +kernel

theorem calc11_set_358_eq : calc11_card_340.envelope ∩ calc11_set_357 = calc11_set_358 := by decide +kernel

theorem calc11_set_359_eq : calc11_card_339.envelope ∩ calc11_set_358 = calc11_set_359 := by decide +kernel

theorem calc11_set_360_eq : calc11_card_338.envelope ∩ calc11_set_359 = calc11_set_360 := by decide +kernel

theorem calc11_set_361_eq : calc11_set_353 ∪ calc11_set_360 = calc11_set_361 := by decide +kernel

theorem calc11_finishA_362 : calc11_set_361.erase (4, 4) = card_706.required := by decide +kernel

theorem calc11_finishT_362 : insert (4, 4) calc11_set_354 = card_706.envelope := by decide +kernel

theorem eq_card_706 : card_706 = combine (4, 4) [placed 7 (8, 6) card_512, placed 5 (1, 6) card_517, placed 7 (8, 6) card_527, placed 7 (8, 6) card_537, inline_809, inline_812, inline_814] := by
  rw [calc11_card_337_eq, calc11_card_338_eq, calc11_card_339_eq, calc11_card_340_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_341_eq, calc11_set_343_eq, calc11_set_345_eq, calc11_set_347_eq, calc11_set_349_eq, calc11_set_351_eq, calc11_set_353_eq, calc11_set_355_eq, calc11_set_356_eq, calc11_set_357_eq, calc11_set_358_eq, calc11_set_359_eq, calc11_set_360_eq, calc11_set_361_eq, calc11_finishA_362]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_342_eq, calc11_set_344_eq, calc11_set_346_eq, calc11_set_348_eq, calc11_set_350_eq, calc11_set_352_eq, calc11_set_354_eq, calc11_finishT_362]
  · decide +kernel

theorem valid_706 : Valid card_706 := by
  rw [eq_card_706]
  apply combination_rule (4, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_512
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 6) valid_517
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_527
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 6) valid_537
  rcases hc with rfl | hc
  · exact valid_inline_809
  rcases hc with rfl | hc
  · exact valid_inline_812
  subst c
  exact valid_inline_814


end OAI.Snaky21.Certificate

theorem solution : Valid card_706 ∧ True :=
  ⟨valid_706, True.intro⟩
